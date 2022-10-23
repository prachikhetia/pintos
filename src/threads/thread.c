  #include "threads/thread.h"
  #include <debug.h>
  #include <stddef.h>
  #include <random.h>
  #include <stdio.h>
  #include <string.h>
  #include "threads/flags.h"
  #include "threads/interrupt.h"
  #include "threads/intr-stubs.h"
  #include "threads/palloc.h"
  #include "threads/switch.h"
  #include "threads/synch.h"
  #include "threads/vaddr.h"

  //including the fixedpoint.h file for fixedpoint calculations
  #include "threads/fixedpoint.h" 

  #ifdef USERPROG
  #include "userprog/process.h"
  #endif

  /* Random value for struct thread's `magic' member.
    Used to detect stack overflow.  See the big comment at the top
    of thread.h for details. */
  #define THREAD_MAGIC 0xcd6abf4b

  /* List of processes in THREAD_READY state, that is, processes
    that are ready to run but not actually running. */
  static struct list ready_list;

  /* A List to store the the threads that are waiting/sleeping */
  static struct list wait_list;

  /* List of all processes.  Processes are added to this list
    when they are first scheduled and removed when they exit. */
  static struct list all_list;

  /* Idle thread. */
  static struct thread *idle_thread;

  /* Initial thread, the thread running init.c:main(). */
  static struct thread *initial_thread;

  /* Lock used by allocate_tid(). */
  static struct lock tid_lock;


  /* Stack frame for kernel_thread(). */
  struct kernel_thread_frame 
    {
      void *eip;                  /* Return address. */
      thread_func *function;      /* Function to call. */
      void *aux;                  /* Auxiliary data for function. */
    };

  /* Statistics. */
  static long long idle_ticks;    /* # of timer ticks spent idle. */
  static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
  static long long user_ticks;    /* # of timer ticks in user programs. */
  static long long total_ticks;    /* # of timer ticks in total. */

  /* Scheduling. */
  #define TIME_SLICE 4            /* # of timer ticks to give each thread. */
  static unsigned thread_ticks;   /* # of timer ticks since last yield. */

  /* If false (default), use round-robin scheduler.
    If true, use multi-level feedback queue scheduler.
    Controlled by kernel command-line option "-o mlfqs". */
  bool thread_mlfqs;

  static void kernel_thread (thread_func *, void *aux);

  static void idle (void *aux UNUSED);
  static struct thread *running_thread (void);
  static struct thread *next_thread_to_run (void);
  static void init_thread (struct thread *, const char *name, int priority);
  static bool is_thread (struct thread *) UNUSED;
  static void *alloc_frame (struct thread *, size_t size);
  static void schedule (void);
  void thread_schedule_tail (struct thread *prev);
  static tid_t allocate_tid (void);
  /*Declaring Value less*/
  static bool value_less (const struct list_elem *, const struct list_elem *,
                          void *);
  static bool wake_earlier (const struct list_elem *, const struct list_elem *,
                          void *);


  //Phase 1.3
  static fixed_point_t  load_avg ;

  /* Initializes the threading system by transforming the code
    that's currently running into a thread.  This can't work in
    general and it is possible in this case only because loader.S
    was careful to put the bottom of the stack at a page boundary.

    Also initializes the run queue and the tid lock.

    After calling this function, be sure to initialize the page
    allocator before trying to create any threads with
    thread_create().

    It is not safe to call thread_current() until this function
    finishes. */
  void
  thread_init (void) 
  {
    ASSERT (intr_get_level () == INTR_OFF);

    lock_init (&tid_lock);
    list_init (&ready_list);
    list_init (&wait_list);
    list_init (&all_list);

    /* Set up a thread structure for the running thread. */
    initial_thread = running_thread ();
    init_thread (initial_thread, "main", PRI_DEFAULT);
    initial_thread->status = THREAD_RUNNING;
    initial_thread->tid = allocate_tid ();

    if ( thread_mlfqs) //If mlfqs mode is true
    {
      //PHASE 1.3
      initial_thread -> recent_cpu = fix_int(0); //add recent_cpu for each thread 
      initial_thread -> nice = 0; //add and initialise nice value to zero for each thread
    }
    load_avg = fix_int(0); //initilize the load_avg value which 
                          //is common for every thread to 0 in fixedpoint type
  }

  /* Starts preemptive thread scheduling by enabling interrupts.
    Also creates the idle thread. */
  void
  thread_start (void) 
  {
    /* Create the idle thread. */
    struct semaphore idle_started;
    sema_init (&idle_started, 0);
    thread_create ("idle", PRI_MIN, idle, &idle_started);

    /* Start preemptive thread scheduling. */
    intr_enable ();

    /* Wait for the idle thread to initialize idle_thread. */
    sema_down (&idle_started);
  }

  /* Called by the timer interrupt handler at each timer tick.
    Thus, this function runs in an external interrupt context. */
  void
  thread_tick (void) 
  {
    struct thread *t = thread_current ();

    /* Update statistics. */
    if (t == idle_thread)
      idle_ticks++;
  #ifdef USERPROG
    else if (t->pagedir != NULL)
      user_ticks++;
  #endif
    else
      kernel_ticks++;

    total_ticks++; 

    struct thread *t2;
    while (!list_empty(&wait_list)) //while wait_list is not empty
    {
      t2 = list_entry (list_front(&wait_list), struct thread, wait_elem); //get the top thread in wait_list
      if (t2->wake_tick > total_ticks) //check if its time to wake not up the top thread.
        break; //break if it is not to be woken up yet.

      //if it is time to wake up the top thread ,
      t2 = list_entry(list_pop_front(&wait_list), struct thread, wait_elem); //pop the top thread
      thread_unblock(t2); //and unblock the top thread

    }

    //PHASE 1.3
  
    if ( thread_mlfqs) //If in mlfqs mode , 
    {

      if (t != idle_thread) //if current thread is not idle_thread
      {
        fixed_point_t oldVal =   thread_current ()->recent_cpu ; //get current recent_cpu value
        thread_current ()->recent_cpu = fix_add( oldVal ,  fix_int(1) );  //increment the recent_cpu value
      }
    }

    /* Enforce preemption. */
    if (++thread_ticks >= TIME_SLICE)
      intr_yield_on_return ();
  }

  /* Prints thread statistics. */
  void
  thread_print_stats (void) 
  {
    printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
            idle_ticks, kernel_ticks, user_ticks);
  }

  /* Creates a new kernel thread named NAME with the given initial
    PRIORITY, which executes FUNCTION passing AUX as the argument,
    and adds it to the ready queue.  Returns the thread identifier
    for the new thread, or TID_ERROR if creation fails.

    If thread_start() has been called, then the new thread may be
    scheduled before thread_create() returns.  It could even exit
    before thread_create() returns.  Contrariwise, the original
    thread may run for any amount of time before the new thread is
    scheduled.  Use a semaphore or some other form of
    synchronization if you need to ensure ordering.

    The code provided sets the new thread's `priority' member to
    PRIORITY, but no actual priority scheduling is implemented.
    Priority scheduling is the goal of Problem 1-3. */
  tid_t
  thread_create (const char *name, int priority,
                thread_func *function, void *aux) 
  {
    struct thread *t;
    struct kernel_thread_frame *kf;
    struct switch_entry_frame *ef;
    struct switch_threads_frame *sf;
    tid_t tid;

    ASSERT (function != NULL);

    /* Allocate thread. */
    t = palloc_get_page (PAL_ZERO);
    if (t == NULL)
      return TID_ERROR;

    /* Initialize thread. */
    init_thread (t, name, priority);
    tid = t->tid = allocate_tid ();

    /* Stack frame for kernel_thread(). */
    kf = alloc_frame (t, sizeof *kf);
    kf->eip = NULL;
    kf->function = function;
    kf->aux = aux;

    /* Stack frame for switch_entry(). */
    ef = alloc_frame (t, sizeof *ef);
    ef->eip = (void (*) (void)) kernel_thread;

    /* Stack frame for switch_threads(). */
    sf = alloc_frame (t, sizeof *sf);
    sf->eip = switch_entry;
    sf->ebp = 0;

    //PHASE 1.3
    if (thread_mlfqs) //If in mlfqs mode
    {
      if (thread_current() == idle_thread) //if current thread is idle_thread
      {
        t -> recent_cpu = fix_int(0); //initialize recent_cpu with 0
        t -> nice = 0;//initialize nice with 0
      }
      else{ //if current thread is not idle_thread
        t -> recent_cpu = thread_current ()->recent_cpu; //initialize the curren_thread with parents recent_cpu
        t -> nice = thread_current ()->nice; //initialize the curren_thread with parents recent_cpu
      }
    }

    /* Add to run queue. */
    thread_unblock (t);
    thread_yield(); //calling thread_yield after it gets added into ready_list
    return tid;
  }

  /* Puts the current thread to sleep.  It will not be scheduled
    again until awoken by thread_unblock().

    This function must be called with interrupts turned off.  It
    is usually a better idea to use one of the synchronization
    primitives in synch.h. */
  void
  thread_block (void) 
  {
    ASSERT (!intr_context ());
    ASSERT (intr_get_level () == INTR_OFF);

    thread_current ()->status = THREAD_BLOCKED;
    schedule ();
  }

  /* Transitions a blocked thread T to the ready-to-run state.
    This is an error if T is not blocked.  (Use thread_yield() to
    make the running thread ready.)

    This function does not preempt the running thread.  This can
    be important: if the caller had disabled interrupts itself,
    it may expect that it can atomically unblock a thread and
    update other data. */
  void
  thread_unblock (struct thread *t) 
  {
    enum intr_level old_level;

    ASSERT (is_thread (t));

    old_level = intr_disable ();
    ASSERT (t->status == THREAD_BLOCKED);


    t->status = THREAD_READY;
    //adding the thread into read_list in a sorted way
    list_insert_ordered(&ready_list ,&t->elem , value_less , NULL );

    intr_set_level (old_level);
  }

  /* Returns the name of the running thread. */
  const char *
  thread_name (void) 
  {
    return thread_current ()->name;
  }

  /* Returns the running thread.
    This is running_thread() plus a couple of sanity checks.
    See the big comment at the top of thread.h for details. */
  struct thread *
  thread_current (void) 
  {
    struct thread *t = running_thread ();
    
    /* Make sure T is really a thread.
      If either of these assertions fire, then your thread may
      have overflowed its stack.  Each thread has less than 4 kB
      of stack, so a few big automatic arrays or moderate
      recursion can cause stack overflow. */
    ASSERT (is_thread (t));
    ASSERT (t->status == THREAD_RUNNING);

    return t;
  }

  /* Returns the running thread's tid. */
  tid_t
  thread_tid (void) 
  {
    return thread_current ()->tid;
  }

  /* Deschedules the current thread and destroys it.  Never
    returns to the caller. */
  void
  thread_exit (void) 
  {
    ASSERT (!intr_context ());

  #ifdef USERPROG
    process_exit ();
  #endif

    /* Remove thread from all threads list, set our status to dying,
      and schedule another process.  That process will destroy us
      when it calls thread_schedule_tail(). */
    intr_disable ();
    list_remove (&thread_current()->allelem);
    thread_current ()->status = THREAD_DYING;
    schedule ();
    NOT_REACHED ();
  }

  /* Yields the CPU.  The current thread is not put to sleep and
    may be scheduled again immediately at the scheduler's whim. */
  void
  thread_yield (void) 
  {
    struct thread *cur = thread_current ();
    enum intr_level old_level;
    
    ASSERT (!intr_context ());
    old_level = intr_disable ();
    if (cur != idle_thread){
      //added the current_thread in ordered way based on priorities
      list_insert_ordered(&ready_list ,&cur->elem ,value_less , NULL ); 
    }
      
    cur->status = THREAD_READY;
    schedule ();
    intr_set_level (old_level);
  }

  /* Invoke function 'func' on all threads, passing along 'aux'.
    This function must be called with interrupts off. */
  void
  thread_foreach (thread_action_func *func, void *aux)
  {
    struct list_elem *e;

    ASSERT (intr_get_level () == INTR_OFF);

    for (e = list_begin (&all_list); e != list_end (&all_list);
        e = list_next (e))
      {
        struct thread *t = list_entry (e, struct thread, allelem);
        func (t, aux);
      }
  }

  /* Sets the current thread's priority to NEW_PRIORITY. */
  void
  thread_set_priority (int new_priority) 
  {
    thread_current ()->base_priority = new_priority; //after updating the priorty 
    update_acting_priority(thread_current()); //calling update_acting_priority on current thread
    thread_yield(); //calling thread_yield to make CPU reschedule the threads based on priorities.
  }

  /* Returns the current thread's priority. */
  int
  thread_get_priority (void) 
  {
    return thread_current ()->priority;
  }

  /* Sets the current thread's nice value to NICE and calss thread_yield */
  void
  thread_set_nice (int nice UNUSED) 
  {
    if(! thread_mlfqs)
    {
      return ;
    }
    //PHASE 1.3
    thread_current ()->nice = nice;
    thread_yield(); 
  }

  /* Returns the current thread's nice value. */
  int
  thread_get_nice (void) 
  {
    if(! thread_mlfqs)
    {
      return 0 ;
    }
    //PHASE 1.3
    return thread_current ()->nice;
  }

  /* Returns 100 times the system load average. */
  int
  thread_get_load_avg (void) 
  {
    return fix_round(fix_mul(load_avg , fix_int(100))); 
  }

  /* Updates load_avg using formula load_avg = (59/60)*load_avg + (1/60)*ready_threads */
  void
  thread_update_load_avg(void)
  {
    if (! thread_mlfqs)
    {
    return ;
    }  
    int ready_threads = list_size(&ready_list);

    if (thread_current() != idle_thread)
    {
      ready_threads = ready_threads+1;
    }
    //calculating coeffiecients of the formula
    fixed_point_t coef_1 = fix_frac(59,60);
    fixed_point_t coef_2 = fix_frac(1,60);

    //calculating numbers 
    fixed_point_t firstNum = fix_mul(coef_1 , load_avg);
    fixed_point_t secondNum = fix_mul(coef_2 , fix_int(ready_threads));

    fixed_point_t sum = fix_add(firstNum , secondNum); //adding those two numbers
    load_avg = sum; //updating the load_avg


  }


  /* Updates the priorty of all threads in all_list when it gets called */
  void
  thread_update_mlfqs_priorty(void) 
  {
      if(!thread_mlfqs) {
        return ;
      }

      struct list_elem *e;

      for (e = list_begin (&all_list); e != list_end (&all_list);
        e = list_next (e)) //for each element in all_list
      {
        struct thread *t = list_entry (e, struct thread, allelem); //get thread from each element
        fixed_point_t recent_cpu = t -> recent_cpu; //access the threads recent_cpu
        int nice = t -> nice; //access the threads nice value
        //calculate the formula using fixedpoint.h functions
        fixed_point_t right = fix_add( fix_div( recent_cpu , fix_int(4))  , (fix_mul(fix_int(nice) , fix_int(2))));
        fixed_point_t val = fix_sub(fix_int( PRI_MAX) , right);
        int prio = fix_trunc(val); //truncates the fixedpoint value to int 
        //limits the priorty to be in between PRI_MIN and PRI_MAX
        if (prio < PRI_MIN ){ 
          prio = PRI_MIN;
        }
        else if (prio > PRI_MAX) {
          prio = PRI_MAX;
        }

        t -> base_priority = prio; //Updates the new priorty
        update_acting_priority(t); //calling update_acting_priorty on the thread t
      }

      list_sort (&ready_list , value_less , NULL ); //sorting the ready_list after updating the priorities

  }


  /* Updates load_avg using formula  recent_cpu = (2*load_avg)/(2*load_avg + 1) * recent_cpu + nice */
  void
  thread_update_recent_cpu(void)
  {

    if (! thread_mlfqs)
    {
      return ;
    }  

      struct list_elem *e;
      
      for (e = list_begin (&all_list); e != list_end (&all_list);
        e = list_next (e)) //for each element in all_list
      {
        struct thread *t = list_entry (e, struct thread, allelem); //get thread from each element
        fixed_point_t oldValue =  t -> recent_cpu ; //access recent_cpu of that thread

        //calculate nice value based on the formula
        fixed_point_t num = fix_mul(fix_int(2) , load_avg);
        fixed_point_t denom = fix_add(num , fix_int(1));
        fixed_point_t coef = fix_div(num , denom);
        fixed_point_t left = fix_mul(coef , oldValue);
        int nice = t -> nice;   //access the current nice
        
        fixed_point_t newVal = fix_add(left , fix_int(nice));
        t -> recent_cpu = newVal;  //update the new recent_cpu
      }



  }



  /* Returns 100 times the current thread's recent_cpu value. */
  int
  thread_get_recent_cpu (void) 
  {
  
    fixed_point_t recent_cpu = thread_current ()->recent_cpu;

    return fix_round(fix_mul(recent_cpu , fix_int(100)));
  }


  
  /* Idle thread.  Executes when no other thread is ready to run.

    The idle thread is initially put on the ready list by
    thread_start().  It will be scheduled once initially, at which
    point it initializes idle_thread, "up"s the semaphore passed
    to it to enable thread_start() to continue, and immediately
    blocks.  After that, the idle thread never appears in the
    ready list.  It is returned by next_thread_to_run() as a
    special case when the ready list is empty. */
  static void
  idle (void *idle_started_ UNUSED) 
  {
    struct semaphore *idle_started = idle_started_;
    idle_thread = thread_current ();
    sema_up (idle_started);

    for (;;) 
      {
        /* Let someone else run. */
        intr_disable ();
        thread_block ();

        /* Re-enable interrupts and wait for the next one.

          The `sti' instruction disables interrupts until the
          completion of the next instruction, so these two
          instructions are executed atomically.  This atomicity is
          important; otherwise, an interrupt could be handled
          between re-enabling interrupts and waiting for the next
          one to occur, wasting as much as one clock tick worth of
          time.

          See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
          7.11.1 "HLT Instruction". */
        asm volatile ("sti; hlt" : : : "memory");
      }
  }

  /* Function used as the basis for a kernel thread. */
  static void
  kernel_thread (thread_func *function, void *aux) 
  {
    ASSERT (function != NULL);
    
    intr_enable ();       /* The scheduler runs with interrupts off. */
    function (aux);       /* Execute the thread function. */
    thread_exit ();       /* If function() returns, kill the thread. */
  }
  
  /* Returns the running thread. */
  struct thread *
  running_thread (void) 
  {
    uint32_t *esp;

    /* Copy the CPU's stack pointer into `esp', and then round that
      down to the start of a page.  Because `struct thread' is
      always at the beginning of a page and the stack pointer is
      somewhere in the middle, this locates the curent thread. */
    asm ("mov %%esp, %0" : "=g" (esp));
    return pg_round_down (esp);
  }

  /* Returns true if T appears to point to a valid thread. */
  static bool
  is_thread (struct thread *t)
  {
    return t != NULL && t->magic == THREAD_MAGIC;
  }

  /* Does basic initialization of T as a blocked thread named
    NAME. */
  static void
  init_thread (struct thread *t, const char *name, int priority)
  {
    enum intr_level old_level;

    ASSERT (t != NULL);
    ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
    ASSERT (name != NULL);

    memset (t, 0, sizeof *t);
    t->status = THREAD_BLOCKED;
    strlcpy (t->name, name, sizeof t->name);
    t->stack = (uint8_t *) t + PGSIZE;
    t->priority = priority;
    t->magic = THREAD_MAGIC;

    t->base_priority = priority; //saving priorty in base_priority variable
    t->lock_waiting_for = NULL; //intializing the lock_waiting_for to NULL
    list_init (&(t->locks_acquired)); //initializing the locks_aquired list of new thread

    old_level = intr_disable ();
    list_push_back (&all_list, &t->allelem);
    intr_set_level (old_level);
  }

  /* Allocates a SIZE-byte frame at the top of thread T's stack and
    returns a pointer to the frame's base. */
  static void *
  alloc_frame (struct thread *t, size_t size) 
  {
    /* Stack data is always allocated in word-size units. */
    ASSERT (is_thread (t));
    ASSERT (size % sizeof (uint32_t) == 0); 

    t->stack -= size;
    return t->stack;
  }

  /* Chooses and returns the next thread to be scheduled.  Should
    return a thread from the run queue, unless the run queue is
    empty.  (If the running thread can continue running, then it
    will be in the run queue.)  If the run queue is empty, return
    idle_thread. */
  static struct thread *
  next_thread_to_run (void) 
  {
    if (list_empty (&ready_list))
      return idle_thread;
    else
      return list_entry (list_pop_front (&ready_list), struct thread, elem);
  }

  /* Completes a thread switch by activating the new thread's page
    tables, and, if the previous thread is dying, destroying it.

    At this function's invocation, we just switched from thread
    PREV, the new thread is already running, and interrupts are
    still disabled.  This function is normally invoked by
    thread_schedule() as its final action before returning, but
    the first time a thread is scheduled it is called by
    switch_entry() (see switch.S).

    It's not safe to call printf() until the thread switch is
    complete.  In practice that means that printf()s should be
    added at the end of the function.

    After this function and its caller returns, the thread switch
    is complete. */
  void
  thread_schedule_tail (struct thread *prev)
  {
    struct thread *cur = running_thread ();
    
    ASSERT (intr_get_level () == INTR_OFF);

    /* Mark us as running. */
    cur->status = THREAD_RUNNING;

    /* Start new time slice. */
    thread_ticks = 0;

  #ifdef USERPROG
    /* Activate the new address space. */
    process_activate ();
  #endif

    /* If the thread we switched from is dying, destroy its struct
      thread.  This must happen late so that thread_exit() doesn't
      pull out the rug under itself.  (We don't free
      initial_thread because its memory was not obtained via
      palloc().) */
    if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread) 
      {
        ASSERT (prev != cur);
        palloc_free_page (prev);
      }
  }

  /* Schedules a new process.  At entry, interrupts must be off and
    the running process's state must have been changed from
    running to some other state.  This function finds another
    thread to run and switches to it.

    It's not safe to call printf() until thread_schedule_tail()
    has completed. */
  static void
  schedule (void) 
  {
    struct thread *cur = running_thread ();
    struct thread *next = next_thread_to_run ();
    struct thread *prev = NULL;

    ASSERT (intr_get_level () == INTR_OFF);
    ASSERT (cur->status != THREAD_RUNNING);
    ASSERT (is_thread (next));

    if (cur != next)
      prev = switch_threads (cur, next);
    thread_schedule_tail (prev);
  }

  /* Returns true if value A is greater than value B, false
  *    otherwise. */
  static bool
  value_less (const struct list_elem *a_, const struct list_elem *b_,
                  void *aux UNUSED) 
  {
      const struct thread *a = list_entry (a_, struct thread, elem);
        const struct thread *b = list_entry (b_, struct thread, elem);
          
          return a->priority > b->priority;
  }

  static bool
  wake_earlier (const struct list_elem *a_, const struct list_elem *b_,
      void *aux UNUSED)
  {
    const struct thread *a = list_entry (a_, struct thread, wait_elem);
    const struct thread *b = list_entry (b_, struct thread, wait_elem);
    return a->wake_tick < b->wake_tick;
  }

  /* Initialise the wake_tick variable of thread , blocks the current thread and adds it to wait_list */
  void
  add_to_wait_list (int64_t wake_tick)
  {
    enum intr_level old_level;
    old_level = intr_disable ();

    struct thread *cur = thread_current (); 
    cur->wake_tick = total_ticks + wake_tick; //calculate and add the ticks at which the thread is to wake up 
    //add the thread in a sorted way , based on earlier thread to wake up is first
    list_insert_ordered(&wait_list ,&cur->wait_elem , wake_earlier , NULL );

    thread_block();
    intr_set_level(old_level); 
   
  }

  /* Returns a tid to use for a new thread. */
  static tid_t
  allocate_tid (void) 
  {
    static tid_t next_tid = 1;
    tid_t tid;

    lock_acquire (&tid_lock);
    tid = next_tid++;
    lock_release (&tid_lock);

    return tid;
  }
  
  /* Offset of `stack' member within `struct thread'.
    Used by switch.S, which can't figure it out on its own. */
  uint32_t thread_stack_ofs = offsetof (struct thread, stack);
