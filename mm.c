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
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "Hyeongjin Song",
    /* Second member's email address (leave blank if none) */
    "x2xgudwls@gmail.com"
};
/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define NEXT(bp) ((char *)(bp) - WSIZE)
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static unsigned int* segregated_free_list[30];


static void init_epilogue(void* start_addr){
    PUT(start_addr + WSIZE, PACK(1,0));
}

static void init_alignment_padding(void* start_addr){
    PUT(start_addr, 0);
}

static int is_heap_over_flow(void* start_addr){
    return start_addr == (void *)-1;
}

static void init_header(void* bp, size_t size){
    PUT(HDRP(bp), PACK(size, 1));
}

static size_t even_number_words_alignment(size_t words){
    if (words % 2){
        return (words+1)*WSIZE;
    }
    return words*WSIZE;
}

static int is_NULL(int index){
    if (segregated_free_list[index] == 0){
        return 1;
    }
    return 0;
}

static int find_index(size_t adjust_size){
    for (int i = 0; i < 30 ; i++){
        if (adjust_size == 1<<(i+3)){
            return i;
        }
    }
}

static void insert_free_list(int index, void* bp){
    PUT(NEXT(bp), segregated_free_list[index]);
    segregated_free_list[index] = bp;
}

static unsigned int* delete_free_list(int index, size_t adjust_size){
    unsigned int* allocated_bp = segregated_free_list[index];
    unsigned int* next_bp = GET(NEXT(segregated_free_list[index]));
    init_header(segregated_free_list[index], adjust_size);
    segregated_free_list[index] = next_bp;
    return allocated_bp;
}

static void divide_chunk(size_t adjust_size, void* bp){
    int index = find_index(adjust_size);
    segregated_free_list[index] = bp;
    while(1){
        if ((char*)bp + adjust_size > mem_heap_hi() - 3){
            PUT(NEXT(bp), 0);
            break;
        }
        PUT(NEXT(bp), (unsigned int*)((char*)bp + adjust_size));
        bp = GET(NEXT(bp));
    }
}

static void* extend_heap(size_t words, size_t adjust_size){
    unsigned int *bp;
    size_t size;
    size = even_number_words_alignment(words);
    bp = mem_sbrk(size);
    if((long)bp == -1){
        return NULL;
    }
    PUT(mem_heap_hi()-3, PACK(0,1));
    divide_chunk(adjust_size, bp);
}

int mm_init(void){
    unsigned int* start_addr = mem_sbrk(2*WSIZE);
    if (is_heap_over_flow(start_addr)) {
        return -1;
    }
    for (int i = 0; i < 30 ; i++){
        segregated_free_list[i] = 0;
    }
    init_alignment_padding(start_addr);
    init_epilogue(start_addr);
    return 0;
}

size_t define_adjust_size(size_t size){
    int n = 0;
    int flag = 0;
    size = size + WSIZE;
    while(1){
        if(size == 1){
            if (flag == 0){
                return 1<<n;
            }
            break;
        }
        flag = flag + (size % 2);
        size = (size) / 2;
        n += 1;
    }
    return 1<<(n+1);
}

void *mm_malloc(size_t size){
    size_t adjust_size;
    size_t extend_size;
    int index;
    unsigned int *bp;
    if (size == 0){
        return NULL;
    }
    adjust_size = define_adjust_size(size);
    index = find_index(adjust_size);
    if(is_NULL(index)){
        extend_size = MAX(adjust_size, CHUNKSIZE);
        bp = extend_heap((extend_size/WSIZE), adjust_size);
        if (is_heap_over_flow(bp)){
            return NULL;
        }
        index = find_index(adjust_size);
        return (void*)delete_free_list(index, adjust_size);
    }
    return (void*)delete_free_list(index, adjust_size);
    
}

void mm_free(void *ptr){
    size_t size = GET_SIZE(HDRP(ptr));
    int index = find_index(size);
    insert_free_list(index, ptr);
}

void *mm_realloc(void *ptr, size_t size){
    if(size <= 0){ 
        mm_free(ptr);
        return 0;
    }
    if(ptr == NULL){
        return mm_malloc(size); 
    }
    void *newp = mm_malloc(size); 
    if(newp == NULL){
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize){
    	oldsize = size; 
	}
    memcpy(newp, ptr, oldsize); 
    mm_free(ptr);
    return newp;
}