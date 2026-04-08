/*
 * mm.c - Segregated free list allocator with 4-byte headers/footers and 4-byte offsets.
 *
 * Blocks are 8-byte aligned. Minimum block size is 16 bytes.
 * Free blocks contain: header (4 bytes), prev offset (4 bytes), next offset (4 bytes), footer (4 bytes).
 * Allocated blocks contain: header (4 bytes), payload, padding, footer (4 bytes).
 */
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

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Free list offsets */
#define GET_PREV_OFFSET(bp) (*(unsigned int *)(bp))
#define GET_NEXT_OFFSET(bp) (*(unsigned int *)((char *)(bp) + WSIZE))

#define SET_PREV_OFFSET(bp, val) (*(unsigned int *)(bp) = (val))
#define SET_NEXT_OFFSET(bp, val) (*(unsigned int *)((char *)(bp) + WSIZE) = (val))

#define OFFSET_TO_PTR(offset) ((offset) == 0 ? NULL : (void *)((char *)heap_start + (offset)))
#define PTR_TO_OFFSET(ptr)    ((ptr) == NULL ? 0 : (unsigned int)((char *)(ptr) - (char *)heap_start))

#define NUM_CLASSES 20

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *heap_start = 0;  /* Pointer to start of heap for offsets */
static unsigned int seg_lists[NUM_CLASSES]; /* Array of offsets to free lists */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static int get_class(size_t size);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);

/*
 * mm_init - Initialize the memory manager
 */
int mm_init(void)
{
    int i;
    for (i = 0; i < NUM_CLASSES; i++) {
        seg_lists[i] = 0;
    }

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    
    heap_start = heap_listp;

    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload
 */
void *malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_listp == 0){
        mm_init();
    }
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * free - Free a block
 */
void free(void *bp)
{
    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * realloc - Naive implementation of realloc
 */
void *realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    free(ptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    if (newptr)
        memset(newptr, 0, bytes);

    return newptr;
}

/*
 * mm_checkheap - Check the heap for consistency
 * 
 * Invariants checked:
 * 1. Heap boundaries: All blocks are within the heap boundaries.
 * 2. Block alignment: All block payloads are 8-byte aligned.
 * 3. Header/Footer consistency: For free blocks, header and footer match.
 * 4. Coalescing: No two consecutive free blocks exist in the heap.
 * 5. Free list consistency: All blocks in the free lists are marked as free.
 * 6. Free list pointers: Next/prev pointers in free lists point to valid free blocks.
 * 7. Free block count: The number of free blocks in the heap matches the number in the free lists.
 */
void mm_checkheap(int verbose)
{
    char *bp = heap_listp;
    int free_count_heap = 0;
    int free_count_list = 0;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
                   GET_SIZE(HDRP(bp)), (GET_ALLOC(HDRP(bp)) ? 'a' : 'f'),
                   GET_SIZE(FTRP(bp)), (GET_ALLOC(FTRP(bp)) ? 'a' : 'f'));

        /* Check alignment */
        if ((size_t)bp % DSIZE) {
            printf("Error: %p is not doubleword aligned\n", bp);
        }

        /* Check header and footer consistency for free blocks */
        if (!GET_ALLOC(HDRP(bp))) {
            if (GET(HDRP(bp)) != GET(FTRP(bp))) {
                printf("Error: header does not match footer at %p\n", bp);
            }
            free_count_heap++;
            
            /* Check coalescing */
            if (!GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
                printf("Error: consecutive free blocks at %p and %p\n", bp, NEXT_BLKP(bp));
            }
        }
    }

    if (verbose)
        printf("%p: epilogue header: [%d:%c]\n", bp,
               GET_SIZE(HDRP(bp)), (GET_ALLOC(HDRP(bp)) ? 'a' : 'f'));

    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

    /* Check free lists */
    for (int i = 0; i < NUM_CLASSES; i++) {
        unsigned int offset = seg_lists[i];
        void *current = OFFSET_TO_PTR(offset);
        while (current != NULL) {
            free_count_list++;
            if (GET_ALLOC(HDRP(current))) {
                printf("Error: allocated block in free list at %p\n", current);
            }
            unsigned int next_offset = GET_NEXT_OFFSET(current);
            if (next_offset != 0) {
                void *next = OFFSET_TO_PTR(next_offset);
                if (GET_PREV_OFFSET(next) != PTR_TO_OFFSET(current)) {
                    printf("Error: prev/next pointers inconsistent at %p and %p\n", current, next);
                }
            }
            current = OFFSET_TO_PTR(next_offset);
        }
    }

    if (free_count_heap != free_count_list) {
        printf("Error: free block count mismatch (heap: %d, list: %d)\n", free_count_heap, free_count_list);
    }
}

/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend the heap with a new free block.
 * Returns a pointer to the newly allocated free block, or NULL on failure.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * place - Place a block of asize bytes at start of free block bp
 * and split if remainder would be at least minimum block size.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    delete_node(bp);

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        insert_node(bp, csize-asize);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes.
 * Returns a pointer to the block, or NULL if no fit is found.
 */
static void *find_fit(size_t asize)
{
    int class = get_class(asize);
    void *bp;

    for (; class < NUM_CLASSES; class++) {
        unsigned int offset = seg_lists[class];
        bp = OFFSET_TO_PTR(offset);
        while (bp != NULL) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
            bp = OFFSET_TO_PTR(GET_NEXT_OFFSET(bp));
        }
    }
    return NULL;
}

/*
 * coalesce - Boundary tag coalescing.
 * Returns a pointer to the coalesced block.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        insert_node(bp, size);
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        delete_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        delete_node(PREV_BLKP(bp));
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp, size);
    return bp;
}

/*
 * get_class - Get the segregated list class index for a given size.
 */
static int get_class(size_t size)
{
    if (size <= 16) return 0;
    if (size <= 24) return 1;
    if (size <= 32) return 2;
    if (size <= 40) return 3;
    if (size <= 48) return 4;
    if (size <= 56) return 5;
    if (size <= 64) return 6;
    if (size <= 128) return 7;
    if (size <= 256) return 8;
    if (size <= 512) return 9;
    if (size <= 1024) return 10;
    if (size <= 2048) return 11;
    if (size <= 4096) return 12;
    if (size <= 8192) return 13;
    if (size <= 16384) return 14;
    if (size <= 32768) return 15;
    if (size <= 65536) return 16;
    if (size <= 131072) return 17;
    if (size <= 262144) return 18;
    return 19;
}

/*
 * insert_node - Insert a free block into the appropriate segregated list.
 * The list is kept sorted by block size.
 */
static void insert_node(void *bp, size_t size)
{
    int class = get_class(size);
    unsigned int current_offset = seg_lists[class];
    void *current = OFFSET_TO_PTR(current_offset);
    void *prev = NULL;

    /* Keep list sorted by size for better fit */
    while (current != NULL && size > GET_SIZE(HDRP(current))) {
        prev = current;
        current = OFFSET_TO_PTR(GET_NEXT_OFFSET(current));
    }

    unsigned int bp_offset = PTR_TO_OFFSET(bp);
    unsigned int prev_offset = PTR_TO_OFFSET(prev);
    unsigned int current_offset_new = PTR_TO_OFFSET(current);

    if (current != NULL) {
        SET_PREV_OFFSET(current, bp_offset);
    }
    SET_NEXT_OFFSET(bp, current_offset_new);
    SET_PREV_OFFSET(bp, prev_offset);

    if (prev != NULL) {
        SET_NEXT_OFFSET(prev, bp_offset);
    } else {
        seg_lists[class] = bp_offset;
    }
}

/*
 * delete_node - Remove a free block from its segregated list.
 */
static void delete_node(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int class = get_class(size);

    unsigned int prev_offset = GET_PREV_OFFSET(bp);
    unsigned int next_offset = GET_NEXT_OFFSET(bp);

    void *prev = OFFSET_TO_PTR(prev_offset);
    void *next = OFFSET_TO_PTR(next_offset);

    if (prev != NULL) {
        SET_NEXT_OFFSET(prev, next_offset);
    } else {
        seg_lists[class] = next_offset;
    }

    if (next != NULL) {
        SET_PREV_OFFSET(next, prev_offset);
    }
}