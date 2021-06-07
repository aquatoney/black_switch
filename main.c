/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright(c) 2010-2016 Intel Corporation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/in.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>

#include <rte_common.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_eal.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_string_fns.h>

#include <rte_icmp.h>
#include <rte_arp.h>
#include <rte_tcp.h>
#include <rte_udp.h>

static volatile bool force_quit;

/* MAC updating enabled by default */
static int mac_updating = 0;

#define RTE_LOGTYPE_L2FWD RTE_LOGTYPE_USER1

#define MAX_PKT_BURST 32
#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */
#define MEMPOOL_CACHE_SIZE 512

/*
 * Configurable number of RX/TX ring descriptors
 */
#define RTE_TEST_RX_DESC_DEFAULT 1024
#define RTE_TEST_TX_DESC_DEFAULT 1024
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;

/* ethernet addresses of ports */
static struct rte_ether_addr l2fwd_ports_eth_addr[RTE_MAX_ETHPORTS];

/* mask of enabled ports */
static uint32_t l2fwd_enabled_port_mask = 0;

/* list of enabled ports */
static uint32_t l2fwd_dst_ports[RTE_MAX_ETHPORTS];

struct port_pair_params {
#define NUM_PORTS	2
	uint16_t port[NUM_PORTS];
} __rte_cache_aligned;

static struct port_pair_params port_pair_params_array[RTE_MAX_ETHPORTS / 2];
static struct port_pair_params *port_pair_params;
static uint16_t nb_port_pair_params;

static unsigned int l2fwd_rx_queue_per_lcore = 1;

#define MAX_RX_QUEUE_PER_LCORE 16
#define MAX_TX_QUEUE_PER_PORT 16
struct lcore_queue_conf {
	unsigned n_rx_port;
	unsigned rx_port_list[MAX_RX_QUEUE_PER_LCORE];
} __rte_cache_aligned;
struct lcore_queue_conf lcore_queue_conf[RTE_MAX_LCORE];

static struct rte_eth_dev_tx_buffer *tx_buffer[RTE_MAX_ETHPORTS];

static struct rte_eth_conf port_conf = {
	.rxmode = {
		.split_hdr_size = 0,
	},
	.txmode = {
		.mq_mode = ETH_MQ_TX_NONE,
	},
};

struct rte_mempool * l2fwd_pktmbuf_pool = NULL;

/* Per-port statistics struct */
struct l2fwd_port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
} __rte_cache_aligned;
struct l2fwd_port_statistics port_statistics[RTE_MAX_ETHPORTS];

#define MAX_TIMER_PERIOD 86400 /* 1 day max */
/* A tsc-based timer responsible for triggering statistics printout */
static uint64_t timer_period = 2; /* default period is 10 seconds */

/* Print out statistics on packets dropped */
static void
print_stats(void)
{
	uint64_t total_packets_dropped, total_packets_tx, total_packets_rx;
	unsigned portid;

	total_packets_dropped = 0;
	total_packets_tx = 0;
	total_packets_rx = 0;

	const char clr[] = { 27, '[', '2', 'J', '\0' };
	const char topLeft[] = { 27, '[', '1', ';', '1', 'H','\0' };

		/* Clear screen and move to top left */
	printf("%s%s", clr, topLeft);

	printf("\nPort statistics ====================================");

	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++) {
		/* skip disabled ports */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;
		printf("\nStatistics for port %u ------------------------------"
			   "\nPackets sent: %24"PRIu64
			   "\nPackets received: %20"PRIu64
			   "\nPackets dropped: %21"PRIu64,
			   portid,
			   port_statistics[portid].tx,
			   port_statistics[portid].rx,
			   port_statistics[portid].dropped);

		total_packets_dropped += port_statistics[portid].dropped;
		total_packets_tx += port_statistics[portid].tx;
		total_packets_rx += port_statistics[portid].rx;
	}
	printf("\nAggregate statistics ==============================="
		   "\nTotal packets sent: %18"PRIu64
		   "\nTotal packets received: %14"PRIu64
		   "\nTotal packets dropped: %15"PRIu64,
		   total_packets_tx,
		   total_packets_rx,
		   total_packets_dropped);
	printf("\n====================================================\n");

	fflush(stdout);
}

/* +++++++++++++++++++++++++++++++++ */
#define DEBUG 0
#define debug_print(fmt, ...) \
            do { if (DEBUG) fprintf(stdout, fmt, __VA_ARGS__); } while (0)


#define LAYER_NUM 3
#define SEG_NUM 5
unsigned normal_order[] = {2, 3, 4};

static void
print_order(unsigned* order, unsigned enter)
{
	for (int i =0; i<LAYER_NUM; i++) {
		printf("%u ", order[i]);
	}
	if (enter) printf("\n");
}

struct seg {
	unsigned start_pos;
	unsigned len;
	unsigned is_branch;
};

struct layer {
	struct seg seg_vec[SEG_NUM];
	unsigned seg_len;
	// unsigned start_pos;
	// unsigned len;
};

static void
push_seg(struct layer* lay, unsigned start_pos, unsigned len, unsigned is_branch)
{
	lay->seg_vec[lay->seg_len].start_pos = start_pos;
	lay->seg_vec[lay->seg_len].len = len;
	lay->seg_vec[lay->seg_len].is_branch = is_branch;
	lay->seg_len ++;
}

#define FOR_EACH_SEG(LAY, SEG) \
	int xxx; \
	if (LAY->seg_len > 0)	   \
		for (xxx=0, SEG=&(LAY->seg_vec[0]); xxx<LAY->seg_len; xxx++, SEG=&(LAY->seg_vec[xxx]))

static void
print_layers(struct layer* layers, unsigned num_layer)
{
	for (unsigned i=0; i<num_layer; i++) {
		printf("layer %u: ", i);
		struct layer* lay = &layers[i];
		struct seg* cur_seg;
		FOR_EACH_SEG(lay, cur_seg) {
			printf("SEG, start: %u, len: %u   ", cur_seg->start_pos, cur_seg->len);
		}
		printf("\n");
	}
	printf("\n");
}

static unsigned 
len_of_layer(struct layer* lay)
{
	unsigned len = 0;
	struct seg* cur_seg;
	FOR_EACH_SEG(lay, cur_seg) {
		len += cur_seg->len;
	}
	// printf("len of layer: %u\n", len);
	return len;
}

static unsigned
len_of_br_seg(struct layer* lay)
{
	unsigned len = 0;
	struct seg* cur_seg;
	FOR_EACH_SEG(lay, cur_seg) {
		if (cur_seg->is_branch) len += cur_seg->len;
	}

	return len;
}

struct branchers {
	rte_be16_t 	ether_type;
	uint8_t	proto;
};

#define L2BRSIZE 2
#define L3BRSIZE 1
#define BRSIZE (L2BRSIZE+L3BRSIZE)

void print_brs(struct branchers* brs)
{
	printf("\n");
	printf("L2: ETH ");
	if (brs->ether_type == rte_cpu_to_be_16(RTE_ETHER_TYPE_IPV4)) {
		printf("L3: IPv4 ");
	}
	else if (brs->ether_type == rte_cpu_to_be_16(RTE_ETHER_TYPE_ARP)) {
		printf("L3: ARP ");
		printf("brs->proto should be -1: %u", brs->proto);
		printf("\n");
		return;
	}
	else {
		printf("L3: unkown ");
	}

	if (brs->proto == IPPROTO_TCP) {
		printf("L4: TCP\n");
	}
	else if (brs->proto == IPPROTO_UDP) {
		printf("L4: UDP\n");
	}
	else if (brs->proto == IPPROTO_ICMP) {
		printf("L4: ICMP\n");
	}
	else {
		printf("L4: unknown\n");
	}

	printf("\n");
}

static void
parse_eth(char* payload, unsigned start_pos, struct layer *layers, unsigned num_layer, struct branchers* brs)
{
	struct rte_ether_hdr *hdr = (struct rte_ether_hdr*)(payload+start_pos);

	push_seg(&layers[num_layer], start_pos, 12, 0);

	/* raw: fake brs */
	if (brs->ether_type == 0) {
		brs->ether_type = hdr->ether_type;
		push_seg(&layers[num_layer], start_pos+12, 2, 1);
	}
	/* disordered: brs from begin */
	else {
		/* ether type from brs, offset 0*/
		push_seg(&layers[num_layer], 0, 2, 1);
	}
}

static void
parse_ip(char* payload, unsigned start_pos, struct layer *layers, unsigned num_layer, struct branchers* brs)
{
	/* can reuse rte_ipv4_hdr even for a broken ipv4, because ihl is not impacted */
	struct rte_ipv4_hdr *hdr = (struct rte_ipv4_hdr *)(payload+start_pos);
	unsigned len = (hdr->version_ihl & 0xf) * 4;

	// printf("ipv4 hdr len: %u\n", len);

	/* first part of IP (before proto) */
	push_seg(&layers[num_layer], start_pos, 9, 0);

	// printf("ip first parsed\n");

	/* do not include proto */
	start_pos += 9;
	/* raw: fake brs */
	if (brs->proto == 0) {
		brs->proto = hdr->next_proto_id;
		push_seg(&layers[num_layer], start_pos, 1, 1);
		start_pos += 1;
	}
	/* disorderred: */
	else {
		/* proto is at offset 2 */
		push_seg(&layers[num_layer], 2, 1, 1);
	}

	/* second part of IP (after proto) */
	push_seg(&layers[num_layer], start_pos, len-9-1, 0);

	// printf("ip parsed, with proto %u\n", brs->proto);

}

static void
parse_arp(char* payload, unsigned start_pos, struct layer *layers, unsigned num_layer, struct branchers* brs)
{
	struct rte_arp_hdr* hdr = (struct rte_arp_hdr*)(payload+start_pos);
	unsigned len = sizeof(struct rte_arp_hdr);

	push_seg(&layers[num_layer], start_pos, len, 0);

	brs->proto = -1;

	// printf("arp parsed\n");
}

static void
parse_tcp(char* payload, unsigned start_pos, struct layer *layers, unsigned num_layer, struct branchers* brs)
{
	struct rte_tcp_hdr* hdr = (struct rte_tcp_hdr*)(payload+start_pos);
	unsigned len = (hdr->data_off & 0xf0) >> 2;
	push_seg(&layers[num_layer], start_pos, len, 0);

	// printf("tcp parsed\n");
}

static void
parse_udp(char* payload, unsigned start_pos, struct layer *layers, unsigned num_layer, struct branchers* brs)
{
	struct rte_udp_hdr* hdr = (struct rte_udp_hdr*)(payload+start_pos);
	unsigned len = sizeof(struct rte_udp_hdr);

	push_seg(&layers[num_layer], start_pos, len, 0);
}

static void
parse_icmp(char* payload, unsigned start_pos, struct layer *layers, unsigned num_layer, struct branchers* brs)
{
	struct rte_icmp_hdr* hdr = (struct rte_icmp_hdr*)(payload+start_pos);
	unsigned len = sizeof(struct rte_icmp_hdr);

	push_seg(&layers[num_layer], start_pos, len, 0);

	// printf("icmp parsed\n");
}

/* swap the field accordingly */
static void
parse_fields(struct rte_mbuf *m, unsigned *cur_order, struct layer* layers, struct branchers* fake_brs)
{	
	char* payload = rte_pktmbuf_mtod(m, char*);

	unsigned num_layers = 0;
	unsigned raw = 0;
	unsigned restore = 0;
	if (CMP_ORDER(normal_order, cur_order) == 0) raw = 1;

	/* 2, 3, 4 in normal order */
	for (int i=0; i<LAYER_NUM; i++) {
		layers[i].seg_len = 0;
	}

	/* 2->3, 3->4 */
	struct branchers* brs = fake_brs;

	unsigned cur_pos;

	// printf("ready to parse packet\n");

	/* fixed 2-3-4 */
	if (raw) {
		cur_pos = 0;
	}
	else {
		/* all branchers are in order of 2->3, 3->4 */
		brs = (struct branchers*)payload;
		unsigned brs_size = brs->ether_type == RTE_ETHER_TYPE_ARP ? L2BRSIZE : BRSIZE;
		// print_brs(brs);
		cur_pos = brs_size;
		debug_print("init cur_pos in disorder case: %u\n", cur_pos);
	}

	for (int i=0; i<LAYER_NUM; i++) {
		unsigned cur_layer = cur_order[i];
		// printf("cur_layer: %u\n", cur_layer);

		if (cur_layer == 2) {
			/* must be Ethernet */
			// printf("cur_pos: %u\n", cur_pos);
			parse_eth(payload, cur_pos, layers, 0, brs);
			cur_pos += len_of_layer(&layers[0]) - (raw ? 0 : len_of_br_seg(&layers[0]));
		}
		else if (cur_layer == 3) {
			// printf("cur_pos: %u\n", cur_pos);
			/* get it from brs->ether_type */
			if (brs->ether_type == rte_cpu_to_be_16(RTE_ETHER_TYPE_IPV4)) {
				parse_ip(payload, cur_pos, layers, 1, brs);
			}
			else if (brs->ether_type == rte_cpu_to_be_16(RTE_ETHER_TYPE_ARP)) {
				parse_arp(payload, cur_pos, layers, 1, brs);
			}
			else {
				// printf("unknown L3 proto\n");
			}
			cur_pos += len_of_layer(&layers[1]) - (raw ? 0 : len_of_br_seg(&layers[1]));
		}
		else if (cur_layer == 4) {
			// printf("cur_pos: %u\n", cur_pos);
			/* no layer 4 */
			if (brs->proto == -1) {
				// printf("no layer 4\n");
				continue;
			}

			/* get if from brs->proto */
			if (brs->proto == IPPROTO_TCP) {
				parse_tcp(payload, cur_pos, layers, 2, brs);
			}
			else if (brs->proto == IPPROTO_UDP) {
				parse_udp(payload, cur_pos, layers, 2, brs);
			}
			else if (brs->proto == IPPROTO_ICMP) {
				parse_icmp(payload, cur_pos, layers, 2, brs);
			}
			else {
				// printf("unknown L4 proto\n");
			}
			cur_pos += len_of_layer(&layers[2]) - (raw ? 0 : len_of_br_seg(&layers[2]));
		}
		else {
			printf("cur_layer goes wrong, %u\n", cur_layer);
		}
	}

}

static void
assemble_fields(struct rte_mbuf* new, struct rte_mbuf* old, unsigned *cur_order, unsigned* target_order, struct layer* layers, struct branchers* brs)
{
	unsigned restore = 0;
	unsigned raw = 0;
	if (CMP_ORDER(normal_order, cur_order) == 0) raw = 1;
	if (CMP_ORDER(normal_order, target_order) == 0) restore = 1;

	char* payload = rte_pktmbuf_mtod(old, char*);
	char* new_payload = rte_pktmbuf_mtod(new, char*);
	unsigned cur_pos = 0;
	unsigned total_copy = 0;

	if (raw && restore) {
		printf("should not appear\n");
		exit(-2);
	}

	unsigned brs_size = brs->ether_type == RTE_ETHER_TYPE_ARP ? L2BRSIZE : BRSIZE;

	/* from disorder/raw to disorder */
	if (!restore) {
		memcpy(new_payload, brs, brs_size);
		cur_pos = brs_size;
	}
	else {
		cur_pos = 0;
	}

	for (int i=0; i<LAYER_NUM; i++) {
		struct layer* cur_lay = &layers[target_order[i]-2];
		struct seg* cur_seg;
		FOR_EACH_SEG(cur_lay, cur_seg) {
			if (restore || !cur_seg->is_branch) {
				debug_print("copying %u (len: %u) from old to new %u\n", cur_seg->start_pos, cur_seg->len, cur_pos);
				memcpy(new_payload+cur_pos, payload+cur_seg->start_pos, cur_seg->len);
				cur_pos += cur_seg->len;
			}
		}
	}

	// printf("original len: %u\n", rte_pktmbuf_pkt_len(m));
	// printf("final pos: %u\n", cur_pos);
	// printf("now len: %u\n", rte_pktmbuf_pkt_len(assemble));
	
	// return assemble;
}

#define NORMAL_PORT 0

#define TABLE_SIZE 10
#define TABLE_FILE "./mac_table.txt"

#define COPY_ORDER(dst, src) \
	memcpy(dst, src, LAYER_NUM*sizeof(unsigned))

#define CMP_ORDER(dst, src) \
	memcmp(dst, src, LAYER_NUM*sizeof(unsigned))

struct mac_rule {
	uint8_t dst_mac[6];
	unsigned target_order[LAYER_NUM];
	unsigned out_port;
};

static void 
print_mac(uint8_t* mac, char enter)
{
	for (int i=0; i<6; i++) {
		printf("%02x", mac[i]);
	}
	if (enter) printf("\n");
}

static void
print_rule(struct mac_rule* rule)
{
	printf("MAC: ");
	print_mac(rule->dst_mac, 0);
	printf("   ORDER: ");
	for (int i=0; i<LAYER_NUM; i++) {
		printf("%u ", rule->target_order[i]);
	}
	printf("   PORT: ");
	printf("%u\n", rule->out_port);
}

struct mac_table {
	struct mac_rule rules[TABLE_SIZE];
	unsigned rule_num;
	unsigned version;
};

static int
match_table(struct mac_table* table, uint8_t* dst_mac)
{
	int matched = -1;
	// printf("matching\n");
	for (int i=0; i<table->rule_num; i++) {
		// printf("matching ");
		// print_mac(dst_mac, 0);
		// printf(" with ");
		// print_mac(table->rules[i].dst_mac, 1);
		if (memcmp(table->rules[i].dst_mac, dst_mac, 6) == 0) {
			matched = i;
			break;
		}

	}
	// printf("matched\n");
	return matched;
}

static void
clear_table(struct mac_table* table)
{
	memset(table->rules, 0, table->rule_num*sizeof(struct mac_rule));
	table->rule_num = 0;
}

static void
print_table(struct mac_table* table)
{
	for (int i=0; i<table->rule_num; i++) {
		print_rule(&table->rules[i]);
	}
	printf("\n");
}

static uint8_t 
hextobin(const char * str, uint8_t * bytes, size_t blen)
{
   uint8_t  pos;
   uint8_t  idx0;
   uint8_t  idx1;

   // mapping of ASCII characters to hex values
   const uint8_t hashmap[] =
   {
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, //  !"#$%&'
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ()*+,-./
     0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, // 01234567
     0x08, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // 89:;<=>?
     0x00, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x00, // @ABCDEFG
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // HIJKLMNO
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // PQRSTUVW
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // XYZ[\]^_
     0x00, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x00, // `abcdefg
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // hijklmno
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // pqrstuvw
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // xyz{|}~.
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ........
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00  // ........
   };

   bzero(bytes, blen);
   for (pos = 0; ((pos < (blen*2)) && (pos < strlen(str))); pos += 2)
   {
      idx0 = (uint8_t)str[pos+0];
      idx1 = (uint8_t)str[pos+1];
      bytes[pos/2] = (uint8_t)(hashmap[idx0] << 4) | hashmap[idx1];
   };

   return(0);
}

static void
add_rule(struct mac_table* table, uint8_t* dst_mac, unsigned* target_order, unsigned out_port)
{
	memcpy(table->rules[table->rule_num].dst_mac, dst_mac, 6);
	COPY_ORDER(table->rules[table->rule_num].target_order, target_order);
	table->rules[table->rule_num].out_port = out_port;

	table->rule_num++;
}

static void
process_rule(struct mac_table* table, char* line)
{
	uint8_t dst_mac[6];
	unsigned target_order[LAYER_NUM];
	unsigned out_port;

	char* field;
	field = strtok(line, " ");
	int index = 1;
	while (field != NULL) {
		// printf("%s\n", field);
		field = strtok(NULL, " ");
		switch (index) {
			/* mac */
			case 1: {
				hextobin(field, dst_mac, 6);
				break;
			}
			/* order */
			case 3: {
				if (strlen(field) != LAYER_NUM) {
					printf("field len (%lu) != LAYER_NUM (%u)\n", strlen(field), LAYER_NUM);
				}
				unsigned order_num = atoi(field);
				for (int i=LAYER_NUM-1; i != -1; i--) {
					target_order[i] = order_num % 10;
					order_num = order_num / 10;
				}
				break;
			}
			/* port */
			case 5: {
				out_port = atoi(field);
				break;
			}
			default: break;
		}
		index++;
	}
	add_rule(table, dst_mac, target_order, out_port);
	printf("\n");
}

static void
update_table(struct mac_table* table)
{
	// printf("updating table\n");
	// print_table(table);

	FILE* fp;
	fp = fopen(TABLE_FILE, "r");
	if (fp == NULL) return;


	char* line = NULL;
	size_t len = 0;
	ssize_t read;

	read = getline(&line, &len, fp);
	if (read == -1) {
		printf("read table file wrong\n");
		fclose(fp);
		return;
	}

	unsigned version = atoi(line);
	if (version == table->version) {
		fclose(fp);
		return;
	}

	clear_table(table);
	table->version = version;
	while ((read = getline(&line, &len, fp)) != -1) {
		process_rule(table, line);		
	}
	fclose(fp);

	if (table->rule_num == 0) {
		printf("no table rule, exit\n");
		exit(-1);
	}

	printf("table updated\n");
	print_table(table);
}

static void
l2fwd_port_forward(struct rte_mbuf *m, unsigned dst_port)
{
	// unsigned dst_port;
	int sent;
	struct rte_eth_dev_tx_buffer *buffer;

	// dst_port = l2fwd_dst_ports[portid];

	buffer = tx_buffer[dst_port];
	sent = rte_eth_tx_buffer(dst_port, 0, buffer, m);
	if (sent)
		port_statistics[dst_port].tx += sent;
}
/* +++++++++++++++++++++++++++++++++ */

static void
l2fwd_simple_forward(struct rte_mbuf *m, unsigned portid)
{
	unsigned dst_port;
	int sent;
	struct rte_eth_dev_tx_buffer *buffer;

	dst_port = l2fwd_dst_ports[portid];

	buffer = tx_buffer[dst_port];
	sent = rte_eth_tx_buffer(dst_port, 0, buffer, m);
	if (sent)
		port_statistics[dst_port].tx += sent;
}


/* main processing loop */
static void
l2fwd_main_loop(void)
{
	struct rte_mbuf *pkts_burst[MAX_PKT_BURST];
	struct rte_mbuf *m;
	int sent;
	unsigned lcore_id;
	uint64_t prev_tsc, diff_tsc, cur_tsc, timer_tsc;
	unsigned i, j, portid, nb_rx;
	struct lcore_queue_conf *qconf;
	const uint64_t drain_tsc = (rte_get_tsc_hz() + US_PER_S - 1) / US_PER_S *
			BURST_TX_DRAIN_US;
	struct rte_eth_dev_tx_buffer *buffer;

	struct mac_table per_core_table;
	unsigned per_core_order[LAYER_NUM];
	per_core_table.rule_num = 0;
	update_table(&per_core_table);
	
	COPY_ORDER(per_core_order, per_core_table.rules[0].target_order);

	prev_tsc = 0;
	timer_tsc = 0;

	lcore_id = rte_lcore_id();
	qconf = &lcore_queue_conf[lcore_id];

	if (qconf->n_rx_port == 0) {
		RTE_LOG(INFO, L2FWD, "lcore %u has nothing to do\n", lcore_id);
		return;
	}

	RTE_LOG(INFO, L2FWD, "entering main loop on lcore %u\n", lcore_id);

	for (i = 0; i < qconf->n_rx_port; i++) {

		portid = qconf->rx_port_list[i];
		RTE_LOG(INFO, L2FWD, " -- lcoreid=%u portid=%u\n", lcore_id,
			portid);

	}

	while (!force_quit) {

		cur_tsc = rte_rdtsc();

		/*
		 * TX burst queue drain
		 */
		diff_tsc = cur_tsc - prev_tsc;
		if (unlikely(diff_tsc > drain_tsc)) {

			for (i = 0; i < qconf->n_rx_port; i++) {

				portid = l2fwd_dst_ports[qconf->rx_port_list[i]];
				buffer = tx_buffer[portid];

				sent = rte_eth_tx_buffer_flush(portid, 0, buffer);
				if (sent)
					port_statistics[portid].tx += sent;

			}

			/* if timer is enabled */
			if (timer_period > 0) {

				/* advance the timer */
				timer_tsc += diff_tsc;

				/* if timer has reached its timeout */
				if (unlikely(timer_tsc >= timer_period)) {
					
					/* do this only on main core */
					// if (lcore_id == rte_get_main_lcore()) {
					// 	print_stats();
					// }
					update_table(&per_core_table);
					COPY_ORDER(per_core_order, per_core_table.rules[0].target_order);
					// printf("updated per core order: ");
					// print_order(per_core_order, 1);
					/* reset the timer */
					timer_tsc = 0;
				}
			}

			prev_tsc = cur_tsc;
		}

		/*
		 * Read packet from RX queues
		 */
		for (i = 0; i < qconf->n_rx_port; i++) {

			portid = qconf->rx_port_list[i];
			nb_rx = rte_eth_rx_burst(portid, 0,
						 pkts_burst, MAX_PKT_BURST);

			port_statistics[portid].rx += nb_rx;

			for (j = 0; j < nb_rx; j++) {
				m = pkts_burst[j];
				rte_prefetch0(rte_pktmbuf_mtod(m, void *));

				unsigned cur_order[3];
				unsigned target_order[3];
				unsigned dst_port = -1;

				// printf("\n\n");
				/* from normal port, meaning it is in 2-3-4 order */
				if (portid == NORMAL_PORT) {
					// printf("coming from normal port\n");
					COPY_ORDER(cur_order, normal_order);
				}
				/* by default we view each packet is in global order (usually disordered) */
				else {
					// printf("non-normal port: ");
					// print_order(per_core_order, 1);
					COPY_ORDER(cur_order, per_core_order);
					// print_order(cur_order, 1);
				}

				struct layer layers[LAYER_NUM];
				struct branchers brs;
				brs.proto = 0;
				brs.ether_type = 0;

				// printf("\nINPUT\n");
				parse_fields(m, cur_order, layers, &brs);
				// print_brs(&real_brs);
				// print_layers(layers, LAYER_NUM);
				// rte_pktmbuf_dump(stdout, m, 64);

				// printf("\nMATCHING\n");
				/* get dst mac addr from layers */
				u_char* payload = rte_pktmbuf_mtod(m, u_char*);
				uint8_t* dst_mac = payload + layers[0].seg_vec[0].start_pos;
				// print_mac(dst_mac, 1);
				int matched = match_table(&per_core_table, dst_mac);
				if (matched < 0) {
					printf("no match for current mac, dropped\n");
					continue;
				}
				else {
					// printf("rule matched\n");
					struct mac_rule *matched_rule = &per_core_table.rules[matched];
					// print_rule(matched_rule);

					COPY_ORDER(target_order, matched_rule->target_order);
					dst_port = matched_rule->out_port;
				}

				/* from normal port, meaning it should be assembled in 2-3-4 order */
				if (dst_port == NORMAL_PORT) {
					// printf("sending to normal port\n");
					COPY_ORDER(target_order, normal_order);
				}

				/* if order is not changed */
				if (CMP_ORDER(cur_order, target_order) == 0) {
					// printf("no change, directly forward to dst_port\n");
					l2fwd_port_forward(m, dst_port);
					continue;
				}

				// printf("\nASSEMBLE\n");
				// struct rte_mbuf* assemble = assemble_fields(m, cur_order, target_order, layers, &brs);
				struct rte_mbuf* clone_mbuf = rte_pktmbuf_copy(m, l2fwd_pktmbuf_pool, 0, 10000000);
				if (clone_mbuf == NULL) {
					printf("mbuf copying wrong\n");
					exit(-1);
				}
				// printf("assembling\n");
				// print_order(cur_order, 1);
				// print_order(target_order, 1);
				assemble_fields(m, clone_mbuf, cur_order, target_order, layers, &brs);
				rte_pktmbuf_free(clone_mbuf);

				// struct layer test_layers[LAYER_NUM];
				// struct branchers test_fake_brs;
				// test_fake_brs.proto = 0;
				// test_fake_brs.ether_type = 0;
				// unsigned test_cur_order[] = {4, 2, 3};
				// unsigned test_target_order[] = {2, 3, 4};

				// printf("\nOUTPUT1\n");
				// parse_fields(m, test_cur_order, test_layers, &test_fake_brs);
				// print_layers(test_layers, LAYER_NUM);
				// rte_pktmbuf_dump(stdout, m, 64);

				// // printf("\nREASSEMBLE\n");
				// struct rte_mbuf* clone_mbuf2 = rte_pktmbuf_copy(m, l2fwd_pktmbuf_pool, 0, 10000000);
				// if (clone_mbuf2 == NULL) {
				// 	printf("mbuf copying wrong\n");
				// 	exit(-1);
				// }

				// assemble_fields(m, clone_mbuf2, test_cur_order, test_target_order, test_layers, &brs);
				// rte_pktmbuf_free(clone_mbuf2);

				// struct layer test2_layers[LAYER_NUM];
				// struct branchers test2_fake_brs;
				// test2_fake_brs.proto = 0;
				// test2_fake_brs.ether_type = 0;
				// unsigned test2_cur_order[] = {2, 3, 4};
				// unsigned test2_target_order[] = {2, 3, 4};

				// printf("\nOUTPUT2\n");
				// parse_fields(m, test2_cur_order, test2_layers, &test2_fake_brs);
				// print_layers(test2_layers, LAYER_NUM);
				// rte_pktmbuf_dump(stdout, m, 64);

				l2fwd_port_forward(m, dst_port);
				// l2fwd_simple_forward(m, portid);
			}
		}
	}
}

static int
l2fwd_launch_one_lcore(__rte_unused void *dummy)
{
	l2fwd_main_loop();
	return 0;
}

/* display usage */
static void
l2fwd_usage(const char *prgname)
{
	printf("%s [EAL options] -- -p PORTMASK [-q NQ]\n"
	       "  -p PORTMASK: hexadecimal bitmask of ports to configure\n"
	       "  -q NQ: number of queue (=ports) per lcore (default is 1)\n"
	       "  -T PERIOD: statistics will be refreshed each PERIOD seconds (0 to disable, 10 default, 86400 maximum)\n"
	       "  --[no-]mac-updating: Enable or disable MAC addresses updating (enabled by default)\n"
	       "      When enabled:\n"
	       "       - The source MAC address is replaced by the TX port MAC address\n"
	       "       - The destination MAC address is replaced by 02:00:00:00:00:TX_PORT_ID\n"
	       "  --portmap: Configure forwarding port pair mapping\n"
	       "	      Default: alternate port pairs\n\n",
	       prgname);
}

static int
l2fwd_parse_portmask(const char *portmask)
{
	char *end = NULL;
	unsigned long pm;

	/* parse hexadecimal string */
	pm = strtoul(portmask, &end, 16);
	if ((portmask[0] == '\0') || (end == NULL) || (*end != '\0'))
		return 0;

	return pm;
}

static int
l2fwd_parse_port_pair_config(const char *q_arg)
{
	enum fieldnames {
		FLD_PORT1 = 0,
		FLD_PORT2,
		_NUM_FLD
	};
	unsigned long int_fld[_NUM_FLD];
	const char *p, *p0 = q_arg;
	char *str_fld[_NUM_FLD];
	unsigned int size;
	char s[256];
	char *end;
	int i;

	nb_port_pair_params = 0;

	while ((p = strchr(p0, '(')) != NULL) {
		++p;
		p0 = strchr(p, ')');
		if (p0 == NULL)
			return -1;

		size = p0 - p;
		if (size >= sizeof(s))
			return -1;

		memcpy(s, p, size);
		s[size] = '\0';
		if (rte_strsplit(s, sizeof(s), str_fld,
				 _NUM_FLD, ',') != _NUM_FLD)
			return -1;
		for (i = 0; i < _NUM_FLD; i++) {
			errno = 0;
			int_fld[i] = strtoul(str_fld[i], &end, 0);
			if (errno != 0 || end == str_fld[i] ||
			    int_fld[i] >= RTE_MAX_ETHPORTS)
				return -1;
		}
		if (nb_port_pair_params >= RTE_MAX_ETHPORTS/2) {
			printf("exceeded max number of port pair params: %hu\n",
				nb_port_pair_params);
			return -1;
		}
		port_pair_params_array[nb_port_pair_params].port[0] =
				(uint16_t)int_fld[FLD_PORT1];
		port_pair_params_array[nb_port_pair_params].port[1] =
				(uint16_t)int_fld[FLD_PORT2];
		++nb_port_pair_params;
	}
	port_pair_params = port_pair_params_array;
	return 0;
}

static unsigned int
l2fwd_parse_nqueue(const char *q_arg)
{
	char *end = NULL;
	unsigned long n;

	/* parse hexadecimal string */
	n = strtoul(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return 0;
	if (n == 0)
		return 0;
	if (n >= MAX_RX_QUEUE_PER_LCORE)
		return 0;

	return n;
}

static int
l2fwd_parse_timer_period(const char *q_arg)
{
	char *end = NULL;
	int n;

	/* parse number string */
	n = strtol(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;
	if (n >= MAX_TIMER_PERIOD)
		return -1;

	return n;
}

static const char short_options[] =
	"p:"  /* portmask */
	"q:"  /* number of queues */
	"T:"  /* timer period */
	;

#define CMD_LINE_OPT_MAC_UPDATING "mac-updating"
#define CMD_LINE_OPT_NO_MAC_UPDATING "no-mac-updating"
#define CMD_LINE_OPT_PORTMAP_CONFIG "portmap"

enum {
	/* long options mapped to a short option */

	/* first long only option value must be >= 256, so that we won't
	 * conflict with short options */
	CMD_LINE_OPT_MIN_NUM = 256,
	CMD_LINE_OPT_PORTMAP_NUM,
};

static const struct option lgopts[] = {
	{ CMD_LINE_OPT_MAC_UPDATING, no_argument, &mac_updating, 1},
	{ CMD_LINE_OPT_NO_MAC_UPDATING, no_argument, &mac_updating, 0},
	{ CMD_LINE_OPT_PORTMAP_CONFIG, 1, 0, CMD_LINE_OPT_PORTMAP_NUM},
	{NULL, 0, 0, 0}
};

/* Parse the argument given in the command line of the application */
static int
l2fwd_parse_args(int argc, char **argv)
{
	int opt, ret, timer_secs;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];

	argvopt = argv;
	port_pair_params = NULL;

	while ((opt = getopt_long(argc, argvopt, short_options,
				  lgopts, &option_index)) != EOF) {

		switch (opt) {
		/* portmask */
		case 'p':
			l2fwd_enabled_port_mask = l2fwd_parse_portmask(optarg);
			if (l2fwd_enabled_port_mask == 0) {
				printf("invalid portmask\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* nqueue */
		case 'q':
			l2fwd_rx_queue_per_lcore = l2fwd_parse_nqueue(optarg);
			if (l2fwd_rx_queue_per_lcore == 0) {
				printf("invalid queue number\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* timer period */
		case 'T':
			timer_secs = l2fwd_parse_timer_period(optarg);
			if (timer_secs < 0) {
				printf("invalid timer period\n");
				l2fwd_usage(prgname);
				return -1;
			}
			timer_period = timer_secs;
			break;

		/* long options */
		case CMD_LINE_OPT_PORTMAP_NUM:
			ret = l2fwd_parse_port_pair_config(optarg);
			if (ret) {
				fprintf(stderr, "Invalid config\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		default:
			l2fwd_usage(prgname);
			return -1;
		}
	}

	if (optind >= 0)
		argv[optind-1] = prgname;

	ret = optind-1;
	optind = 1; /* reset getopt lib */
	return ret;
}

/*
 * Check port pair config with enabled port mask,
 * and for valid port pair combinations.
 */
static int
check_port_pair_config(void)
{
	uint32_t port_pair_config_mask = 0;
	uint32_t port_pair_mask = 0;
	uint16_t index, i, portid;

	for (index = 0; index < nb_port_pair_params; index++) {
		port_pair_mask = 0;

		for (i = 0; i < NUM_PORTS; i++)  {
			portid = port_pair_params[index].port[i];
			if ((l2fwd_enabled_port_mask & (1 << portid)) == 0) {
				printf("port %u is not enabled in port mask\n",
				       portid);
				return -1;
			}
			if (!rte_eth_dev_is_valid_port(portid)) {
				printf("port %u is not present on the board\n",
				       portid);
				return -1;
			}

			port_pair_mask |= 1 << portid;
		}

		if (port_pair_config_mask & port_pair_mask) {
			printf("port %u is used in other port pairs\n", portid);
			return -1;
		}
		port_pair_config_mask |= port_pair_mask;
	}

	l2fwd_enabled_port_mask &= port_pair_config_mask;

	return 0;
}

/* Check the link status of all ports in up to 9s, and print them finally */
static void
check_all_ports_link_status(uint32_t port_mask)
{
#define CHECK_INTERVAL 100 /* 100ms */
#define MAX_CHECK_TIME 90 /* 9s (90 * 100ms) in total */
	uint16_t portid;
	uint8_t count, all_ports_up, print_flag = 0;
	struct rte_eth_link link;
	int ret;
	char link_status_text[RTE_ETH_LINK_MAX_STR_LEN];

	printf("\nChecking link status");
	fflush(stdout);
	for (count = 0; count <= MAX_CHECK_TIME; count++) {
		if (force_quit)
			return;
		all_ports_up = 1;
		RTE_ETH_FOREACH_DEV(portid) {
			if (force_quit)
				return;
			if ((port_mask & (1 << portid)) == 0)
				continue;
			memset(&link, 0, sizeof(link));
			ret = rte_eth_link_get_nowait(portid, &link);
			if (ret < 0) {
				all_ports_up = 0;
				if (print_flag == 1)
					printf("Port %u link get failed: %s\n",
						portid, rte_strerror(-ret));
				continue;
			}
			/* print link status if flag set */
			if (print_flag == 1) {
				rte_eth_link_to_str(link_status_text,
					sizeof(link_status_text), &link);
				printf("Port %d %s\n", portid,
				       link_status_text);
				continue;
			}
			/* clear all_ports_up flag if any link down */
			if (link.link_status == ETH_LINK_DOWN) {
				all_ports_up = 0;
				break;
			}
		}
		/* after finally printing all link status, get out */
		if (print_flag == 1)
			break;

		if (all_ports_up == 0) {
			printf(".");
			fflush(stdout);
			rte_delay_ms(CHECK_INTERVAL);
		}

		/* set the print_flag if all ports up or timeout */
		if (all_ports_up == 1 || count == (MAX_CHECK_TIME - 1)) {
			print_flag = 1;
			printf("done\n");
		}
	}
}

static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n",
				signum);
		force_quit = true;
	}
}

int
main(int argc, char **argv)
{
	struct lcore_queue_conf *qconf;
	int ret;
	uint16_t nb_ports;
	uint16_t nb_ports_available = 0;
	uint16_t portid, last_port;
	unsigned lcore_id, rx_lcore_id;
	unsigned nb_ports_in_mask = 0;
	unsigned int nb_lcores = 0;
	unsigned int nb_mbufs;

	/* init EAL */
	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid EAL arguments\n");
	argc -= ret;
	argv += ret;

	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);

	/* parse application arguments (after the EAL ones) */
	ret = l2fwd_parse_args(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid L2FWD arguments\n");

	printf("MAC updating %s\n", mac_updating ? "enabled" : "disabled");

	/* convert to number of cycles */
	timer_period *= rte_get_timer_hz();

	nb_ports = rte_eth_dev_count_avail();
	if (nb_ports == 0)
		rte_exit(EXIT_FAILURE, "No Ethernet ports - bye\n");

	if (port_pair_params != NULL) {
		if (check_port_pair_config() < 0)
			rte_exit(EXIT_FAILURE, "Invalid port pair config\n");
	}

	/* check port mask to possible port mask */
	if (l2fwd_enabled_port_mask & ~((1 << nb_ports) - 1))
		rte_exit(EXIT_FAILURE, "Invalid portmask; possible (0x%x)\n",
			(1 << nb_ports) - 1);

	/* reset l2fwd_dst_ports */
	for (portid = 0; portid < RTE_MAX_ETHPORTS; portid++)
		l2fwd_dst_ports[portid] = 0;
	last_port = 0;

	/* populate destination port details */
	if (port_pair_params != NULL) {
		uint16_t idx, p;

		for (idx = 0; idx < (nb_port_pair_params << 1); idx++) {
			p = idx & 1;
			portid = port_pair_params[idx >> 1].port[p];
			l2fwd_dst_ports[portid] =
				port_pair_params[idx >> 1].port[p ^ 1];
		}
	} else {
		RTE_ETH_FOREACH_DEV(portid) {
			/* skip ports that are not enabled */
			if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
				continue;

			if (nb_ports_in_mask % 2) {
				l2fwd_dst_ports[portid] = last_port;
				l2fwd_dst_ports[last_port] = portid;
			} else {
				last_port = portid;
			}

			nb_ports_in_mask++;
		}
		if (nb_ports_in_mask % 2) {
			printf("Notice: odd number of ports in portmask.\n");
			l2fwd_dst_ports[last_port] = last_port;
		}
	}

	rx_lcore_id = 0;
	qconf = NULL;

	/* Initialize the port/queue configuration of each logical core */
	RTE_ETH_FOREACH_DEV(portid) {
		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;

		/* get the lcore_id for this port */
		while (rte_lcore_is_enabled(rx_lcore_id) == 0 ||
		       lcore_queue_conf[rx_lcore_id].n_rx_port ==
		       l2fwd_rx_queue_per_lcore) {
			rx_lcore_id++;
			if (rx_lcore_id >= RTE_MAX_LCORE)
				rte_exit(EXIT_FAILURE, "Not enough cores\n");
		}

		if (qconf != &lcore_queue_conf[rx_lcore_id]) {
			/* Assigned a new logical core in the loop above. */
			qconf = &lcore_queue_conf[rx_lcore_id];
			nb_lcores++;
		}

		qconf->rx_port_list[qconf->n_rx_port] = portid;
		qconf->n_rx_port++;
		printf("Lcore %u: RX port %u TX port %u\n", rx_lcore_id,
		       portid, l2fwd_dst_ports[portid]);
	}

	nb_mbufs = RTE_MAX(nb_ports * (nb_rxd + nb_txd + MAX_PKT_BURST +
		nb_lcores * MEMPOOL_CACHE_SIZE), 8192U);

	/* create the mbuf pool */
	l2fwd_pktmbuf_pool = rte_pktmbuf_pool_create("mbuf_pool", nb_mbufs,
		MEMPOOL_CACHE_SIZE, 0, RTE_MBUF_DEFAULT_BUF_SIZE,
		rte_socket_id());
	if (l2fwd_pktmbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot init mbuf pool\n");

	/* Initialise each port */
	RTE_ETH_FOREACH_DEV(portid) {
		struct rte_eth_rxconf rxq_conf;
		struct rte_eth_txconf txq_conf;
		struct rte_eth_conf local_port_conf = port_conf;
		struct rte_eth_dev_info dev_info;

		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0) {
			printf("Skipping disabled port %u\n", portid);
			continue;
		}
		nb_ports_available++;

		/* init port */
		printf("Initializing port %u... ", portid);
		fflush(stdout);

		ret = rte_eth_dev_info_get(portid, &dev_info);
		if (ret != 0)
			rte_exit(EXIT_FAILURE,
				"Error during getting device (port %u) info: %s\n",
				portid, strerror(-ret));

		if (dev_info.tx_offload_capa & DEV_TX_OFFLOAD_MBUF_FAST_FREE)
			local_port_conf.txmode.offloads |=
				DEV_TX_OFFLOAD_MBUF_FAST_FREE;
		ret = rte_eth_dev_configure(portid, 1, 1, &local_port_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "Cannot configure device: err=%d, port=%u\n",
				  ret, portid);

		ret = rte_eth_dev_adjust_nb_rx_tx_desc(portid, &nb_rxd,
						       &nb_txd);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
				 "Cannot adjust number of descriptors: err=%d, port=%u\n",
				 ret, portid);

		ret = rte_eth_macaddr_get(portid,
					  &l2fwd_ports_eth_addr[portid]);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
				 "Cannot get MAC address: err=%d, port=%u\n",
				 ret, portid);

		/* init one RX queue */
		fflush(stdout);
		rxq_conf = dev_info.default_rxconf;
		rxq_conf.offloads = local_port_conf.rxmode.offloads;
		ret = rte_eth_rx_queue_setup(portid, 0, nb_rxd,
					     rte_eth_dev_socket_id(portid),
					     &rxq_conf,
					     l2fwd_pktmbuf_pool);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_rx_queue_setup:err=%d, port=%u\n",
				  ret, portid);

		/* init one TX queue on each port */
		fflush(stdout);
		txq_conf = dev_info.default_txconf;
		txq_conf.offloads = local_port_conf.txmode.offloads;
		ret = rte_eth_tx_queue_setup(portid, 0, nb_txd,
				rte_eth_dev_socket_id(portid),
				&txq_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup:err=%d, port=%u\n",
				ret, portid);

		/* Initialize TX buffers */
		tx_buffer[portid] = rte_zmalloc_socket("tx_buffer",
				RTE_ETH_TX_BUFFER_SIZE(MAX_PKT_BURST), 0,
				rte_eth_dev_socket_id(portid));
		if (tx_buffer[portid] == NULL)
			rte_exit(EXIT_FAILURE, "Cannot allocate buffer for tx on port %u\n",
					portid);

		rte_eth_tx_buffer_init(tx_buffer[portid], MAX_PKT_BURST);

		ret = rte_eth_tx_buffer_set_err_callback(tx_buffer[portid],
				rte_eth_tx_buffer_count_callback,
				&port_statistics[portid].dropped);
		if (ret < 0)
			rte_exit(EXIT_FAILURE,
			"Cannot set error callback for tx buffer on port %u\n",
				 portid);

		ret = rte_eth_dev_set_ptypes(portid, RTE_PTYPE_UNKNOWN, NULL,
					     0);
		if (ret < 0)
			printf("Port %u, Failed to disable Ptype parsing\n",
					portid);
		/* Start device */
		ret = rte_eth_dev_start(portid);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_dev_start:err=%d, port=%u\n",
				  ret, portid);

		printf("done: \n");

		ret = rte_eth_promiscuous_enable(portid);
		if (ret != 0)
			rte_exit(EXIT_FAILURE,
				 "rte_eth_promiscuous_enable:err=%s, port=%u\n",
				 rte_strerror(-ret), portid);

		printf("Port %u, MAC address: %02X:%02X:%02X:%02X:%02X:%02X\n\n",
				portid,
				l2fwd_ports_eth_addr[portid].addr_bytes[0],
				l2fwd_ports_eth_addr[portid].addr_bytes[1],
				l2fwd_ports_eth_addr[portid].addr_bytes[2],
				l2fwd_ports_eth_addr[portid].addr_bytes[3],
				l2fwd_ports_eth_addr[portid].addr_bytes[4],
				l2fwd_ports_eth_addr[portid].addr_bytes[5]);

		/* initialize port stats */
		memset(&port_statistics, 0, sizeof(port_statistics));
	}

	if (!nb_ports_available) {
		rte_exit(EXIT_FAILURE,
			"All available ports are disabled. Please set portmask.\n");
	}

	check_all_ports_link_status(l2fwd_enabled_port_mask);

	ret = 0;
	/* launch per-lcore init on every lcore */
	rte_eal_mp_remote_launch(l2fwd_launch_one_lcore, NULL, CALL_MAIN);
	RTE_LCORE_FOREACH_WORKER(lcore_id) {
		if (rte_eal_wait_lcore(lcore_id) < 0) {
			ret = -1;
			break;
		}
	}

	RTE_ETH_FOREACH_DEV(portid) {
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;
		printf("Closing port %d...", portid);
		ret = rte_eth_dev_stop(portid);
		if (ret != 0)
			printf("rte_eth_dev_stop: err=%d, port=%d\n",
			       ret, portid);
		rte_eth_dev_close(portid);
		printf(" Done\n");
	}
	printf("Bye...\n");

	return ret;
}
