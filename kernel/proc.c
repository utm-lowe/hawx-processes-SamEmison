#include "types.h"
#include "memlayout.h"
#include "elf.h"
#include "riscv.h"
#include "mem.h"
#include "string.h"
#include "console.h"
#include "trap.h"
#include "proc.h"

// Extern Globals
extern pagetable_t kernel_pagetable; // mem.c
extern char trampoline[]; // trampoline.S
extern char _binary_user_init_start; // The user init code

////////////////////////////////////////////////////////////////////////////////
// Static Definitions and Helper Function Prototypes
////////////////////////////////////////////////////////////////////////////////
static int nextpid = 1;
static pagetable_t proc_pagetable(struct proc*);
static void proc_free_pagetable(pagetable_t pagetable, uint64 sz);
static void proc_freewalk(pagetable_t pagetable);
static uint64 proc_shrink(pagetable_t pagetable, uint64 oldsz, uint64 newsz);
static int proc_loadseg(pagetable_t pagetable, uint64 va, void *bin, uint offset, uint sz);
static void proc_guard(pagetable_t pagetable, uint64 va);


////////////////////////////////////////////////////////////////////////////////
// Global Definitions
////////////////////////////////////////////////////////////////////////////////
struct cpu cpu;
struct proc proc[NPROC];




////////////////////////////////////////////////////////////////////////////////
// Process API Functions 
////////////////////////////////////////////////////////////////////////////////

// Initialize the proc table, and allocate a page for each process's 
// kernel stack. Map the stacks in high memory, followed by an invalid guard page.
void 
proc_init(void)
{
    struct proc *p;
    for(p = proc; p < &proc[NPROC]; p++){
        p->kstack = KSTACK((int)(p - proc));
        void *pa = vm_page_alloc();
        if(!pa){
            panic("proc_init: vm_page_alloc failed");
        }
        if(vm_page_insert(kernel_pagetable, p->kstack, (uint64)pa, PTE_R | PTE_W) < 0){
            vm_page_free(pa);
            panic("proc_init: vm_page_insert failed");
        }
    }
}



// Set up the first user process. Return the process it was allocated to.
struct proc*
proc_load_user_init(void)
{
    void *bin = &_binary_user_init_start;
    struct proc *p = 0x00;

    p = proc_alloc();
    if(!p){
        panic("proc_load_user_init: proc_alloc failed");
    }
    if(proc_load_elf(p, bin) < 0){
        proc_free(p);
        panic("proc_load_user_init: proc_load_elf failed");
    }

    return p;
}


// Look in the process table for an UNUSED proc.
// If found, initialize state required to run in the kernel,
// and return with p->lock held.
// If there are no free procs, or a memory allocation fails, return 0.
struct proc* 
proc_alloc(void)
{
    struct proc *p;
    
    for(p = proc; p < &proc[NPROC]; p++){
        if(p->state == UNUSED){
            goto found;
        }
    }
    return 0;

found:
    p->pid = nextpid++;
    
    // Allocate trapframe page
    if((p->trapframe = (struct trapframe *)vm_page_alloc()) == 0){
        p->state = UNUSED;
        return 0;
    }
    memset(p->trapframe, 0, sizeof(*p->trapframe));
    
    // Allocate page table
    if((p->pagetable = proc_pagetable(p)) == 0){
        vm_page_free((void *)p->trapframe);
        p->trapframe = 0;
        p->state = UNUSED;
        return 0;
    }
    
    // Set up context for usertrapret
    p->context.ra = (uint64)usertrapret;
    p->context.sp = p->kstack + PGSIZE;
    
    p->state = USED;
    return p;
}


// free a proc structure and the data hanging from it,
// including user pages.
void 
proc_free(struct proc *p)
{
    if(p->trapframe){
        vm_page_free((void *)p->trapframe);
        p->trapframe = 0;
    }
    if(p->pagetable){
        proc_free_pagetable(p->pagetable, p->sz);
        p->pagetable = 0;
    }
    p->sz = 0;
    p->pid = 0;
    p->state = UNUSED;
}


// Load the ELF program image stored in the binary string bin
// into the specified process. This operation will destroy the 
// pagetable currently in p, and replace it with a page table
// as indicated by the segments of the elf formatted binary.
int
proc_load_elf(struct proc *p, void *bin)
{
    struct elfhdr elf;
    struct proghdr ph;
    int i, off;
    uint64 sz=0, sp=0;
    pagetable_t pagetable=0;

    // get the elf header from bin
    elf = *(struct elfhdr*) bin;

    // check the elf magic
    if(elf.magic != ELF_MAGIC)
        goto bad;

    // Create a new pagetable for the process
    pagetable = proc_pagetable(p);
    if(pagetable == 0)
        goto bad;

    // Load each program segment
    for(i = 0; i < elf.phnum; i++){
        off = elf.phoff + i*elf.phentsize;
        if(off + sizeof(ph) > PGSIZE * 8){
            goto bad;
        }
        ph = *(struct proghdr*)(((char *)bin) + off);
        
        if(ph.type != ELF_PROG_LOAD)
            continue;
        
        if(ph.memsz < ph.filesz){
            goto bad;
        }
        if(ph.vaddr + ph.memsz < ph.vaddr){
            goto bad;
        }
        if(ph.vaddr % PGSIZE != 0){
            goto bad;
        }
        
        // Resize the process to accommodate this segment
        uint64 newsz = ph.vaddr + ph.memsz;
        if(proc_resize(pagetable, sz, newsz) != newsz){
            goto bad;
        }
        sz = newsz;
        
        // Load the segment
        if(proc_loadseg(pagetable, ph.vaddr, bin, ph.off, ph.filesz) < 0){
            goto bad;
        }
    }

    // Allocate space for the stack
    uint64 newsz = PGROUNDUP(sz);
    newsz += 2 * PGSIZE; // One page for the stack, one for guard
    if(proc_resize(pagetable, sz, newsz) != newsz){
        goto bad;
    }
    sz = newsz;
    sp = sz;
    
    // Mark the stack guard page as inaccessible
    proc_guard(pagetable, sp - 2*PGSIZE);

    // Set up the trapframe
    struct trapframe *tf = p->trapframe;
    memset(tf, 0, sizeof(*tf));
    tf->epc = elf.entry;
    tf->sp = sp;
    tf->kernel_satp = MAKE_SATP(kernel_pagetable);
    tf->kernel_sp = p->kstack + PGSIZE;
    tf->kernel_trap = (uint64)usertrapret;
    tf->kernel_hartid = r_tp();

    // Free the old page table and commit to the new one
    proc_free_pagetable(p->pagetable, p->sz);
    p->pagetable = pagetable;
    p->sz = sz;
    p->state = RUNNABLE;
    
    return 0;

bad:
    if(pagetable){
        proc_free_pagetable(pagetable, sz);
    }
    return -1;
}


// Resize the process so that it occupies newsz bytes of memory.
// If newsz > oldsz
//   Allocate PTEs and physical memory to grow process from oldsz to
// If newsz < oldsz
//   Use proc_shrink to decrease the zie of the process.
// newsz, which need not be page aligned.  Returns new size or 0 on error.
uint64 proc_resize(pagetable_t pagetable, uint64 oldsz, uint64 newsz) 
{
    if(newsz > oldsz){
        // Allocate new pages
        int npages = (PGROUNDUP(newsz) - PGROUNDUP(oldsz)) / PGSIZE;
        for(int i = 0; i < npages; i++){
            void *pa = vm_page_alloc();
            if(!pa){
                proc_shrink(pagetable, newsz, oldsz);
                return 0;
            }
            // Clear the page
            memset(pa, 0, PGSIZE);
            // Calculate virtual address and permissions
            uint64 va = PGROUNDUP(oldsz) + i*PGSIZE;
            int perm = PTE_W | PTE_R | PTE_X | PTE_U;
            if(vm_page_insert(pagetable, va, (uint64)pa, perm) < 0){
                vm_page_free(pa);
                proc_shrink(pagetable, newsz, oldsz);
                return 0;
            }
        }
        return newsz;
    }
    else if(newsz < oldsz){
        return proc_shrink(pagetable, oldsz, newsz);
    }
    return oldsz;
}


// Given a parent process's page table, copy its memory into a 
// child's page table. Copies both the page table and the physical
// memory.
int 
proc_vmcopy(pagetable_t old, pagetable_t new, uint64 sz)
{
  uint64 i;
  uint64 pa;
  pte_t *pte_old;

  for(i = 0; i < sz; i += PGSIZE){
    pte_old = walk_pgtable(old, i, 0);
    if(pte_old == 0){
      continue;
    }
    if((*pte_old & PTE_V) == 0){
      continue;
    }
    
    pa = PTE2PA(*pte_old);
    void *new_pa = vm_page_alloc();
    if(new_pa == 0){
      return -1;
    }
    
    // Copy the page
    memmove(new_pa, (void*)pa, PGSIZE);
    
    // Insert into new page table with same permissions
    if(vm_page_insert(new, i, (uint64)new_pa, PTE_FLAGS(*pte_old)) < 0){
      vm_page_free(new_pa);
      return -1;
    }
  }
  return 0;
}


////////////////////////////////////////////////////////////////////////////////
// Static Helper Functions
////////////////////////////////////////////////////////////////////////////////

// Create a user page table for a given process,
// with no user memory, but with trampoline pages.
static pagetable_t 
proc_pagetable(struct proc *p)
{
    pagetable_t pagetable;

    pagetable = vm_create_pagetable();
    if(pagetable == 0)
        return 0;

    // Map trampoline
    if(vm_page_insert(pagetable, TRAMPOLINE, (uint64)trampoline, PTE_R | PTE_X) < 0){
        vm_page_free((void*)pagetable);
        return 0;
    }

    // Map trapframe
    if(vm_page_insert(pagetable, TRAPFRAME, (uint64)(p->trapframe), PTE_R | PTE_W) < 0){
        vm_page_remove(pagetable, TRAMPOLINE, 1, 0);
        vm_page_free((void*)pagetable);
        return 0;
    }

    return pagetable;
}



// Free a process's page table, and free the
// physical memory it refers to.
static void 
proc_free_pagetable(pagetable_t pagetable, uint64 sz)
{
    // Remove trampoline and trapframe mappings
    vm_page_remove(pagetable, TRAMPOLINE, 1, 0);
    vm_page_remove(pagetable, TRAPFRAME, 1, 0);
    
    // Remove user memory pages
    uint64 num_user_pages = PGROUNDUP(sz) / PGSIZE;
    if(num_user_pages > 0){
        vm_page_remove(pagetable, 0, num_user_pages, 1);
    }
    
    // Free the page table itself
    proc_freewalk(pagetable);
}



// Recursively free page-table pages.
// All leaf mappings must already have been removed.
static void 
proc_freewalk(pagetable_t pagetable)
{
  // there are 2^9 = 512 PTEs in a page table.
  for(int i = 0; i < 512; i++){
    pte_t pte = pagetable[i];
    if((pte & PTE_V) && (pte & (PTE_R|PTE_W|PTE_X)) == 0){
      // this PTE points to a lower-level page table.
      uint64 child = PTE2PA(pte);
      proc_freewalk((pagetable_t)child);
      pagetable[i] = 0;
    } else if(pte & PTE_V){
      panic("freewalk: leaf");
    }
  }
  vm_page_free((void*)pagetable);
}


// Deallocate user pages to bring the process size from oldsz to
// newsz.  oldsz and newsz need not be page-aligned, nor does newsz
// need to be less than oldsz.  oldsz can be larger than the actual
// process size.  Returns the new process size.
static uint64 
proc_shrink(pagetable_t pagetable, uint64 oldsz, uint64 newsz)
{
  if(newsz >= oldsz)
    return oldsz;

  if(PGROUNDUP(newsz) < PGROUNDUP(oldsz)){
    int npages = (PGROUNDUP(oldsz) - PGROUNDUP(newsz)) / PGSIZE;
    vm_page_remove(pagetable, PGROUNDUP(newsz), npages, 1);
  }

  return newsz;
}


// Load a program segment into pagetable at virtual address va.
// va must be page-aligned
// and the pages from va to va+sz must already be mapped.
// Returns 0 on success, -1 on failure.
static int
proc_loadseg(pagetable_t pagetable, uint64 va, void *bin, uint offset, uint sz)
{
  uint i, n;
  uint64 pa;

  for(i = 0; i < sz; i += PGSIZE){
    uint64 vaddr = va + i;
    pa = vm_lookup(pagetable, vaddr);
    if(pa == 0){
      return -1;
    }
    
    n = sz - i;
    if(n > PGSIZE)
      n = PGSIZE;
    
    memmove((void *)pa, (char *)bin + offset + i, n);
  }
  
  return 0;
}


// mark a PTE invalid for user access.
// used by proc_load_elf for the user stack guard page.
static void 
proc_guard(pagetable_t pagetable, uint64 va)
{
    pte_t *pte;

    pte = walk_pgtable(pagetable, va, 0);
    if(pte == 0)
        panic("proc_guard");
    *pte &= ~PTE_U;
}

// Find the process with the given pid and return a pointer to it.
// If the process is not found, return 0
struct proc *proc_find(int pid) {
  for(int i=0; i<NPROC; i++){
    if(proc[i].pid == pid){
      return &proc[i];
    }
  } 
  return 0;
}