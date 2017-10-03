/*
 * This header comment gives a high level description of our solution.
 * Our allocator aligns our block to double word boundaries. We define the size of a word, WSIZE, by using the size of a pointer.
 * Our allocated and free blocks have 4 byte headers and footers containing the block's size and allocation.
 * Free blocks have pointers following the header, containing pointers to the next and previous blocks in the explicit free list. 
 * These are both 8 bytes long each; thus each of our blocks will have a size of at least (8+8+4+4=24) bytes.
 * We use an explicit, doubly linked free list to keep track of the free blocks in the heap.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/



/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))

/* Basic constants and macros */
#define WSIZE 4 /* Byte size of: header, footer, word */
#define DSIZE 8 /* Byte size of: doubleword */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(x, y) ((x) > (y) ? (x) : (y))


/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val) | GET_TAG(p))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p) (GET(p) & 0x2)


/* Given block ptr bp, comPUTe address of its header and footer */
#define HDRP(bp)  ((void *)(bp) - WSIZE)
#define FTRP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, comPUTe address of next and previous blocks */
#define NEXT_BLKP(bp)  ((void *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)  ((void *)(bp) - GET_SIZE((void *)(bp) - DSIZE))

/* Given pointer in the free list, GET the next and previous pointers */
#define NEXT(bp) (*(char **) (bp+WSIZE))
#define PREV(bp) (*(char **) (bp))

/* Sets next and previous elements in the free list */
#define SETNEXT(bp, cp) (NEXT(bp) = cp)
#define SETPREV(bp, cp) (PREV(bp) = cp)

/* Global declarations of things */
static char* heap_listp;
static char* lstart;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *fit(size_t asize);
static void place(void *bp, size_t asize);
static void remove_from_list(void *bp);
static void add_to_list(void *bp);

/*
 * add_to_list - adds bp to the free list
*/
static void add_to_list(void *bp){
    SETNEXT(bp, lstart);
    SETPREV(lstart, bp);
    SETPREV(bp, NULL);
    lstart = bp;
}


/*
 * remove_from_list - removes bp from the free list
*/
static void remove_from_list(void *bp){
    if (PREV(bp))
        SETNEXT(PREV(bp), NEXT(bp));
    else
        lstart = NEXT(bp);
    SETPREV(NEXT(bp), PREV(bp));
}

/*
 * place - places a block of # asize bytes at the start of bp, then splits if the remainder is at least the min block size
*/
static void place(void *bp, size_t size){
    size_t updated = GET_SIZE(HDRP(bp));
    
    if ((updated - size) >= 4 * WSIZE) 
    {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        remove_from_list(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(updated-size, 0));
        PUT(FTRP(bp), PACK(updated-size, 0));
        coalesce(bp);
    }
    else 
    {
        PUT(HDRP(bp), PACK(updated, 1));
        PUT(FTRP(bp), PACK(updated, 1));
        remove_from_list(bp);
    }
}


/*
 * coalesce - coalesces the boundary tags and returns the address of the block once coalesced 
*/
static void *coalesce(void *bp){
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))  );
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))  ) || PREV_BLKP(bp) == bp;
    size_t size = GET_SIZE(HDRP(bp));
    /* Multiple cases: */
    if (prev_alloc && !next_alloc) // 1: only next is free
    {  
        size += GET_SIZE( HDRP(NEXT_BLKP(bp)));
        remove_from_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) // 2: only prev is free
    {  
        size += GET_SIZE( HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        remove_from_list(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && !next_alloc) // 3: both are free
    {  
        size += GET_SIZE( HDRP(PREV_BLKP(bp))  ) + GET_SIZE( HDRP(NEXT_BLKP(bp))  );
        remove_from_list(PREV_BLKP(bp));
        remove_from_list(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Final insertion into free list */
    add_to_list(bp);
    return bp;
}

/*
 * extend_heap - extends the heap with a free block; returns its address
*/
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t sizeholder;
    sizeholder = (words % 2) ? (words+1) * WSIZE : words * WSIZE;  // maintains alignment
    if (sizeholder < 16)
    {
        sizeholder = 16;
	}
    if ((int)(bp = mem_sbrk(sizeholder)) == -1) // calls for more space in memory
    {  
        return NULL;
    }
    PUT(HDRP(bp), PACK(sizeholder, 0));
    PUT(FTRP(bp), PACK(sizeholder, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    return coalesce(bp);
}


/*
 * fit - finds a fit for a block; returns the block's address, or NULL
*/
static void *fit(size_t size)
{
    void *bp;
    static int lm_size = 0;
    static int repcount = 0;
    if(lm_size == (int)size)
    {
        if(repcount>30)
        {
            int DoubleNewSize = MAX(size, 4 * WSIZE);
            bp = extend_heap(DoubleNewSize/4);
            return bp;
        }
        else
            repcount=repcount+1;
    }
    else
        repcount = 0;
    for (bp = lstart; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT(bp))
    {
        if (size <= (size_t)GET_SIZE(HDRP(bp))) 
        {
            lm_size = size;
            return bp;
        }
    }
    return NULL;
}

/* 
 * mm_init - initialize the malloc package
*/
int mm_init(void)
{
    
    if ((heap_listp = mem_sbrk(8*WSIZE)) == NULL)
        return -1;
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    lstart = heap_listp + 2*WSIZE;
    
    if (extend_heap(4) == NULL)
    {
        return -1;
    }
    return 0;
}

/* This function will free a block beginning of address "pointer," and coalesce*/
void mm_free(void *pointer)
{
    size_t sizes=GET_SIZE(HDRP(pointer));
  if (pointer == NULL)
    return;
  PUT(HDRP(pointer), PACK(sizes, 0));
  PUT(FTRP(pointer), PACK(sizes, 0));
  coalesce(pointer);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 *      Returns the address of the block if allocation is successful; otherwise, NULL.
*/
void *mm_malloc(size_t size) 
{
  size_t asize; /*Adjusted block size*/
  size_t extendsize; /* Amount to extend heap, if no fit */
  void *bp=NULL; 

  /* Base case: you do not need to allocate if size is zero */
  if (size == 0)
    return (NULL);

  /* Consider alignment conerns */
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
      asize=ALIGN((size+DSIZE));

  if ((bp = fit(asize)) != NULL)
  {
    place(bp, asize);
    return (bp);
  }

  /* Worst case: no fit, so we must extend heap */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return (NULL);
  place(bp, asize);
  return (bp);
} 

/*
 * mm_realloc - reallocates the block bp to a block with at least the number of bytes of the payload. 
*/
void *mm_realloc(void *bp, size_t size)
{
   if((int)size <= 0)
   {
        return NULL;
   }
    else if(size > 0)
    {
        size_t HeadSize = GET_SIZE(HDRP(bp));
        size_t updatedsize = size + 2 * WSIZE;
        if(updatedsize <= HeadSize)
        {
            return bp;
        }
        
        
        else
        {
            size_t newallocated = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
            size_t sizes;
            if(!newallocated && ((sizes = HeadSize + GET_SIZE(HDRP(NEXT_BLKP(bp))))) >= updatedsize)
            {
                remove_from_list(NEXT_BLKP(bp));
                PUT(HDRP(bp), PACK(sizes, 1));
                PUT(FTRP(bp), PACK(sizes, 1));
                return bp;
            }
            else
            {
                void *updatedPointer = mm_malloc(updatedsize);
                place(updatedPointer, updatedsize);
                memcpy(updatedPointer, bp, updatedsize);
                mm_free(bp);
                return updatedPointer; 
            } 
        }
    }
    else
    {
        return NULL;
    }
}

