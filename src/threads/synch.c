/* This file is derived from source code for the Nachos
   instructional operating system.  The Nachos copyright notice
   is reproduced in full below. */

/* Copyright (c) 1992-1996 The Regents of the University of California.
   All rights reserved.

   Permission to use, copy, modify, and distribute this software
   and its documentation for any purpose, without fee, and
   without written agreement is hereby granted, provided that the
   above copyright notice and the following two paragraphs appear
   in all copies of this software.

   IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO
   ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR
   CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE
   AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA
   HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

   THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY
   WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
   PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS"
   BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO
   PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
   MODIFICATIONS.
*/

#include "threads/synch.h"
#include <stdio.h>
#include <string.h>
#include "threads/interrupt.h"
#include "threads/thread.h"

/* Initializes semaphore SEMA to VALUE.  A semaphore is a
   nonnegative integer along with two atomic operators for
   manipulating it:

   - down or "P": wait for the value to become positive, then
     decrement it.

   - up or "V": increment the value (and wake up one waiting
     thread, if any). */
void
sema_init (struct semaphore *sema, unsigned value) 
{
  ASSERT (sema != NULL);

  sema->value = value;
  list_init (&sema->waiters);
}
/* Returns true if value A is greater than value B, false
 *    otherwise. */
static bool value_less (const struct list_elem *, const struct list_elem *,
                        void *);

static bool
value_less (const struct list_elem *a_, const struct list_elem *b_,
                void *aux UNUSED) 
{
    const struct thread *a = list_entry (a_, struct thread, elem);
      const struct thread *b = list_entry (b_, struct thread, elem);
        
        return a->priority > b->priority;
}
/* Down or "P" operation on a semaphore.  Waits for SEMA's value
   to become positive and then atomically decrements it.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but if it sleeps then the next scheduled
   thread will probably turn interrupts back on. */
void
sema_down (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);
  ASSERT (!intr_context ());

  old_level = intr_disable ();
  while (sema->value == 0) 
    {
      //Adding the current thread into waiters list of the semaphore in ordered/sorted way
      list_insert_ordered(&sema->waiters ,&thread_current ()->elem , value_less , NULL );
      //calling update_acting_priorty on current thread.
      update_acting_priority(thread_current());
      thread_block ();
    }
  sema->value--;
  intr_set_level (old_level);
}

/* Down or "P" operation on a semaphore, but only if the
   semaphore is not already 0.  Returns true if the semaphore is
   decremented, false otherwise.

   This function may be called from an interrupt handler. */
bool
sema_try_down (struct semaphore *sema) 
{
  enum intr_level old_level;
  bool success;

  ASSERT (sema != NULL);

  old_level = intr_disable ();
  if (sema->value > 0) 
    {
      sema->value--;
      success = true; 
    }
  else
    success = false;
  intr_set_level (old_level);

  return success;
}

/* Up or "V" operation on a semaphore.  Increments SEMA's value
   and wakes up one thread of those waiting for SEMA, if any.

   This function may be called from an interrupt handler. */
void
sema_up (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);

  old_level = intr_disable ();
  if (!list_empty (&sema->waiters))
  { 
    //sorting the waiters list because the priority of the waiters might have got updated 
    list_sort (&sema->waiters, value_less, NULL);
    thread_unblock (list_entry (list_pop_front (&sema->waiters),
                                struct thread, elem));
  }
  sema->value++;
  thread_yield();
  intr_set_level (old_level);
}

static void sema_test_helper (void *sema_);

/* Self-test for semaphores that makes control "ping-pong"
   between a pair of threads.  Insert calls to printf() to see
   what's going on. */
void
sema_self_test (void) 
{
  struct semaphore sema[2];
  int i;

  printf ("Testing semaphores...");
  sema_init (&sema[0], 0);
  sema_init (&sema[1], 0);
  thread_create ("sema-test", PRI_DEFAULT, sema_test_helper, &sema);
  for (i = 0; i < 10; i++) 
    {
      sema_up (&sema[0]);
      sema_down (&sema[1]);
    }
  printf ("done.\n");
}

/* Thread function used by sema_self_test(). */
static void
sema_test_helper (void *sema_) 
{
  struct semaphore *sema = sema_;
  int i;

  for (i = 0; i < 10; i++) 
    {
      sema_down (&sema[0]);
      sema_up (&sema[1]);
    }
}

/* Initializes LOCK.  A lock can be held by at most a single
   thread at any given time.  Our locks are not "recursive", that
   is, it is an error for the thread currently holding a lock to
   try to acquire that lock.

   A lock is a specialization of a semaphore with an initial
   value of 1.  The difference between a lock and such a
   semaphore is twofold.  First, a semaphore can have a value
   greater than 1, but a lock can only be owned by a single
   thread at a time.  Second, a semaphore does not have an owner,
   meaning that one thread can "down" the semaphore and then
   another one "up" it, but with a lock the same thread must both
   acquire and release it.  When these restrictions prove
   onerous, it's a good sign that a semaphore should be used,
   instead of a lock. */
void
lock_init (struct lock *lock)
{
  ASSERT (lock != NULL);

  lock->holder = NULL;
  sema_init (&lock->semaphore, 1);
}

/* Acquires LOCK, sleeping until it becomes available if
   necessary.  The lock must not already be held by the current
   thread.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
lock_acquire (struct lock *lock)
{
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (!lock_held_by_current_thread (lock));
//adding LOCK as lock_waiting_for 
  thread_current()->lock_waiting_for = lock;
  sema_down (&lock->semaphore);//Trying to aquire the the resource
  thread_current()->lock_waiting_for = NULL;//If successfull , making it back to NULL

  lock->holder = thread_current ();
  //adding the current lock into current_threads lock_aquired list
  list_push_back (&thread_current()->locks_acquired, &lock->lock_elem);
}

/* Tries to acquires LOCK and returns true if successful or false
   on failure.  The lock must not already be held by the current
   thread.

   This function will not sleep, so it may be called within an
   interrupt handler. */
bool
lock_try_acquire (struct lock *lock)
{
  bool success;

  ASSERT (lock != NULL);
  ASSERT (!lock_held_by_current_thread (lock));

  //adding LOCK as lock_waiting_for 
  thread_current()->lock_waiting_for = lock;
  success = sema_try_down (&lock->semaphore);//Trying to aquire the the resource
  thread_current()->lock_waiting_for = NULL;//If successfull , making it back to NULL

  if (success) //if successfull
  {
    lock->holder = thread_current ();
    //adding the current lock into current_threads lock_aquired list
    list_push_back (&thread_current()->locks_acquired, &lock->lock_elem);
  }
  return success;
}
/* Gets the maximum of all the threads that are waiting on *T and *T's base Priorty , 
and updates its acting priorty. If *T is waiting on another thread  , calls update_acting_priority on it too*/
void
update_acting_priority(struct thread *t)
{
  int mx = t->base_priority; //get the base priority into mx,mx has the highest priority
  struct list_elem *lock; 
  if (!list_empty(&t->locks_acquired)) 
  {
    //loops on locks_aquired , accesses each thread waiting on those locks and updates
    // mx variable to store the highest priority.
    for (lock = list_begin(&t->locks_acquired); lock != list_end(&t->locks_acquired);
	  lock = list_next(lock))
    {
      struct lock *lck = list_entry(lock, struct lock, lock_elem); 
      struct semaphore *sema = &lck->semaphore; 
      if (!list_empty(&sema->waiters)) 
      {
        struct list_elem *child_waiter = list_begin(&sema->waiters); 
        struct thread *child = list_entry(child_waiter, struct thread, elem);
       
        mx = max_func(mx, child->priority);
      }
    }
  }
  t->priority = mx; //update priorty with highest priorty of its childs and base priorty

  if (t->lock_waiting_for != NULL && t->lock_waiting_for->holder != 0x0) //if current thread is waiting for other thread
  { 
    //Update the parent thread 
    
    //remove the current thread from list of the waiters of lock_waiting_for
    // and adding it back into the waiters list sorted by acting_priorty (*T -> PRIORITY).
    list_remove(&t->elem); 
    struct semaphore *sema = &t->lock_waiting_for->semaphore; 
    list_insert_ordered(&sema->waiters, &t->elem, value_less, NULL); 
    update_acting_priority(t->lock_waiting_for->holder); //calling the same function on its parent
  }
}

//1.3
int
max_func(int a, int b) //return maximum of a and b
{
  return (a > b) ? a : b;
}



/* Releases LOCK, which must be owned by the current thread.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to release a lock within an interrupt
   handler. */
void
lock_release (struct lock *lock) 
{
  ASSERT (lock != NULL);
  ASSERT (lock_held_by_current_thread (lock));
//remove the lock from the threads locks_acquired list
  list_remove (&lock->lock_elem);
  lock->holder = NULL;
  enum intr_level old_level;
  old_level = intr_disable ();
  update_acting_priority(thread_current()); //update the priorty of the thread , after releasing
  sema_up (&lock->semaphore);
  intr_set_level (old_level); //setting interrupts back
  
  
}

/* Returns true if the current thread holds LOCK, false
   otherwise.  (Note that testing whether some other thread holds
   a lock would be racy.) */
bool
lock_held_by_current_thread (const struct lock *lock) 
{
  ASSERT (lock != NULL);

  return lock->holder == thread_current ();
}

/* One semaphore in a list. */
struct semaphore_elem 
  {
    struct list_elem elem;              /* List element. */
    struct semaphore semaphore;         /* This semaphore. */
  };

static bool sema_value_less (const struct list_elem *, const struct list_elem *,
                        void *);

static bool
sema_value_less (const struct list_elem *a_, const struct list_elem *b_,
                void *aux UNUSED)
{
    struct semaphore *a = &list_entry (a_, struct semaphore_elem, elem)->semaphore;
    struct semaphore *b = &list_entry (b_, struct semaphore_elem, elem)->semaphore;

    const struct thread *t_a = list_entry (list_begin(&a->waiters), struct thread, elem);
    const struct thread *t_b = list_entry (list_begin(&b->waiters), struct thread, elem);

    return t_a->priority > t_b->priority;
}


/* Initializes condition variable COND.  A condition variable
   allows one piece of code to signal a condition and cooperating
   code to receive the signal and act upon it. */
void
cond_init (struct condition *cond)
{
  ASSERT (cond != NULL);

  list_init (&cond->waiters);
}

/* Atomically releases LOCK and waits for COND to be signaled by
   some other piece of code.  After COND is signaled, LOCK is
   reacquired before returning.  LOCK must be held before calling
   this function.

   The monitor implemented by this function is "Mesa" style, not
   "Hoare" style, that is, sending and receiving a signal are not
   an atomic operation.  Thus, typically the caller must recheck
   the condition after the wait completes and, if necessary, wait
   again.

   A given condition variable is associated with only a single
   lock, but one lock may be associated with any number of
   condition variables.  That is, there is a one-to-many mapping
   from locks to condition variables.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
cond_wait (struct condition *cond, struct lock *lock) 
{
  struct semaphore_elem waiter;

  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));
  
  sema_init (&waiter.semaphore, 0);
  list_push_back (&cond->waiters, &waiter.elem);
  lock_release (lock);
  sema_down (&waiter.semaphore);
  lock_acquire (lock);
}

/* If any threads are waiting on COND (protected by LOCK), then
   this function signals one of them to wake up from its wait.
   LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_signal (struct condition *cond, struct lock *lock UNUSED) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));

  if (!list_empty (&cond->waiters)) 
  {
    //sorting the waiters list before , cuz it will help in popping up the lock with highest priorty thread
    list_sort(&cond->waiters,sema_value_less,NULL);
    sema_up (&list_entry (list_pop_front (&cond->waiters),
         struct semaphore_elem, elem)->semaphore);
  }
}

/* Wakes up all threads, if any, waiting on COND (protected by
   LOCK).  LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_broadcast (struct condition *cond, struct lock *lock) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);

  while (!list_empty (&cond->waiters))
    cond_signal (cond, lock);
}
