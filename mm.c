#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc, prev_alloc)  ((size) | (alloc) | ((prev_alloc) << 1))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) ((GET(p) & 0x2) >> 1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Free list pointers */
#define PRED_PTR(bp) ((char *)(bp))
#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)

#define PRED(bp) (*(unsigned int *)(bp) == 0 ? NULL : base_ptr + *(unsigned int *)(bp))
#define SUCC(bp) (*(unsigned int *)(SUCC_PTR(bp)) == 0 ? NULL : base_ptr + *(unsigned int *)(SUCC_PTR(bp)))

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (ptr) == NULL ? 0 : (unsigned int)((char *)(ptr) - base_ptr))

#define LIST_COUNT 20

static char *heap_listp = 0;
static char *base_ptr = 0;
static char *segregated_free_lists[LIST_COUNT];

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *place(void *bp, size_t asize);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);
static int get_list_index(size_t size);

int mm_init(void) {
    int i;
    for (i = 0; i < LIST_COUNT; i++) {
        segregated_free_lists[i] = NULL;
    }

    if ((base_ptr = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    heap_listp = base_ptr;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0, prev_alloc));
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0));

    return coalesce(bp);
}

static void insert_node(void *bp, size_t size) {
    int list_idx = get_list_index(size);
    void *search_ptr = segregated_free_lists[list_idx];
    void *insert_ptr = NULL;

    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = SUCC(search_ptr);
    }

    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(bp), insert_ptr);
            SET_PTR(SUCC_PTR(bp), search_ptr);
            SET_PTR(SUCC_PTR(insert_ptr), bp);
            SET_PTR(PRED_PTR(search_ptr), bp);
        } else {
            SET_PTR(PRED_PTR(bp), NULL);
            SET_PTR(SUCC_PTR(bp), search_ptr);
            SET_PTR(PRED_PTR(search_ptr), bp);
            segregated_free_lists[list_idx] = bp;
        }
    } else {
        if (insert_ptr != NULL) {
            SET_PTR(PRED_PTR(bp), insert_ptr);
            SET_PTR(SUCC_PTR(bp), NULL);
            SET_PTR(SUCC_PTR(insert_ptr), bp);
        } else {
            SET_PTR(PRED_PTR(bp), NULL);
            SET_PTR(SUCC_PTR(bp), NULL);
            segregated_free_lists[list_idx] = bp;
        }
    }
}

static void delete_node(void *bp) {
    int list_idx = get_list_index(GET_SIZE(HDRP(bp)));
    if (PRED(bp) != NULL) {
        if (SUCC(bp) != NULL) {
            SET_PTR(SUCC_PTR(PRED(bp)), SUCC(bp));
            SET_PTR(PRED_PTR(SUCC(bp)), PRED(bp));
        } else {
            SET_PTR(SUCC_PTR(PRED(bp)), NULL);
        }
    } else {
        if (SUCC(bp) != NULL) {
            SET_PTR(PRED_PTR(SUCC(bp)), NULL);
            segregated_free_lists[list_idx] = SUCC(bp);
        } else {
            segregated_free_lists[list_idx] = NULL;
        }
    }
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        insert_node(bp, size);
        return bp;
    } else if (prev_alloc && !next_alloc) {
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0, 1));
        PUT(FTRP(bp), PACK(size, 0, 1));
    } else if (!prev_alloc && next_alloc) {
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0, prev_prev_alloc));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, prev_prev_alloc));
        bp = PREV_BLKP(bp);
    } else {
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0, prev_prev_alloc));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0, prev_prev_alloc));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp, size);
    return bp;
}

void *malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp = NULL;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE - 1)) / DSIZE);

    int list_idx = get_list_index(asize);
    int i;
    for (i = list_idx; i < LIST_COUNT; i++) {
        bp = segregated_free_lists[i];
        while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))) {
            bp = SUCC(bp);
        }
        if (bp != NULL)
            break;
    }

    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
            return NULL;
    }

    bp = place(bp, asize);
    return bp;
}

static void *place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize;
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    delete_node(bp);

    if (remainder >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1, prev_alloc));
        char *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(remainder, 0, 1));
        PUT(FTRP(next_bp), PACK(remainder, 0, 1));
        insert_node(next_bp, remainder);
    } else {
        PUT(HDRP(bp), PACK(csize, 1, prev_alloc));
        char *next_bp = NEXT_BLKP(bp);
        size_t next_size = GET_SIZE(HDRP(next_bp));
        size_t next_alloc = GET_ALLOC(HDRP(next_bp));
        PUT(HDRP(next_bp), PACK(next_size, next_alloc, 1));
        if (!next_alloc) {
            PUT(FTRP(next_bp), PACK(next_size, next_alloc, 1));
        }
    }
    return bp;
}

void free(void *bp) {
    if (bp == NULL)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0, prev_alloc));
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));
    
    char *next_bp = NEXT_BLKP(bp);
    size_t next_size = GET_SIZE(HDRP(next_bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    PUT(HDRP(next_bp), PACK(next_size, next_alloc, 0));
    if (!next_alloc) {
        PUT(FTRP(next_bp), PACK(next_size, next_alloc, 0));
    }

    coalesce(bp);
}

void *realloc(void *ptr, size_t size) {
    if (size == 0) {
        free(ptr);
        return NULL;
    }
    if (ptr == NULL) {
        return malloc(size);
    }

    size_t asize;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE - 1)) / DSIZE);

    size_t old_size = GET_SIZE(HDRP(ptr));
    if (old_size >= asize) {
        return ptr;
    }

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

    if (!next_alloc && (old_size + next_size >= asize)) {
        delete_node(NEXT_BLKP(ptr));
        size_t remainder = old_size + next_size - asize;
        size_t prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
        if (remainder >= (2 * DSIZE)) {
            PUT(HDRP(ptr), PACK(asize, 1, prev_alloc));
            char *next_bp = NEXT_BLKP(ptr);
            PUT(HDRP(next_bp), PACK(remainder, 0, 1));
            PUT(FTRP(next_bp), PACK(remainder, 0, 1));
            insert_node(next_bp, remainder);
        } else {
            PUT(HDRP(ptr), PACK(old_size + next_size, 1, prev_alloc));
            char *next_bp = NEXT_BLKP(ptr);
            size_t nn_size = GET_SIZE(HDRP(next_bp));
            size_t nn_alloc = GET_ALLOC(HDRP(next_bp));
            PUT(HDRP(next_bp), PACK(nn_size, nn_alloc, 1));
            if (!nn_alloc) {
                PUT(FTRP(next_bp), PACK(nn_size, nn_alloc, 1));
            }
        }
        return ptr;
    }

    void *new_ptr = malloc(size);
    if (new_ptr == NULL)
        return NULL;

    memcpy(new_ptr, ptr, old_size - WSIZE);
    free(ptr);
    return new_ptr;
}

void *calloc(size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr = malloc(bytes);
    if (newptr != NULL) {
        memset(newptr, 0, bytes);
    }
    return newptr;
}

static int get_list_index(size_t size) {
    if (size <= 16) return 0;
    if (size <= 32) return 1;
    if (size <= 64) return 2;
    if (size <= 128) return 3;
    if (size <= 256) return 4;
    if (size <= 512) return 5;
    if (size <= 1024) return 6;
    if (size <= 2048) return 7;
    if (size <= 4096) return 8;
    if (size <= 8192) return 9;
    if (size <= 16384) return 10;
    if (size <= 32768) return 11;
    if (size <= 65536) return 12;
    if (size <= 131072) return 13;
    if (size <= 262144) return 14;
    if (size <= 524288) return 15;
    if (size <= 1048576) return 16;
    if (size <= 2097152) return 17;
    if (size <= 4194304) return 18;
    return 19;
}

void mm_checkheap(int verbose) {
    (void)verbose;
}
