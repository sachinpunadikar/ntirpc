/*
 * Copyright (c) 2017 IBM Corporation.
 * All rights reserved.
 */
#ifndef RPC_DPLX_GFD_H
#define RPC_DPLX_GFD_H

#include <stdint.h>

/*
 * Callers close fd and then remove the corresponding rpc_dplx_rec
 * hashtable entry. With this, it is possible that a thread might get
 * same fd number before an old thread could remove the entry from the
 * hashtable, and this new thread might grab unrelated rpc_dplx_rec
 * entry. Use generation number as a key into hash table.
 */
struct gfd {
	int fd;
	uint64_t gen;
};

/* Get generation number for fd */
extern uint64_t rpc_get_next_fdgen(void);

#endif
