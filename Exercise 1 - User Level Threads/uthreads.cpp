//
// Created by yotam on 06/06/2024.
//

// all included libraries  //
#include <csignal>
#include <cstdlib>
#include <queue>
#include <csetjmp>
#include <algorithm>
#include <iostream>
#include "uthreads.h"
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <list>
#include <sys/time.h>


// defined integer values //
#define FAILED -1
#define EXIT_FAIL 1
#define GREAT_SUCCESS 0
#define MIN_VALID_QUANTUM 1
#define MAIN_THREAD_TID 0
#define MAX_THREAD_NUM 100
#define STACK_SIZE 4096


// defined string values //
#define THREADS_LIBRARY_ERROR "thread library error: "
#define SYSTEM_CALL_ERROR "system error: "
#define NON_POSITIVE_USECS "This function should get only positive values."
#define SET_SIGNAL_HANDLER_FAILED "failed to set signal handler."
#define SET_TIMER_FAILED "failed to set the time."
#define ENTRY_NULLPTR "entry point cannot be nullptr."
#define MAX_THREADS_REACHED "no space for new thread."
#define THREAD_NULLPTR "there is no thread with this ID."
#define BLOCK_MAIN_THREAD "cannot block main thread."
#define SLEEP_MAIN_THREAD "main thread can't sleep."
#define MASK_SIGNAL_MESSAGE(how) (how == SIG_BLOCK ? "block signal failed" : \
                                        "unblock signal failed")

#ifdef __x86_64__
/* code for 64 bit Intel arch */

typedef unsigned long address_t;
#define JB_SP 6
#define JB_PC 7


/* A translation is required when using an address of a variable.
   Use this as a black box in your code. */
address_t translate_address(address_t addr)
{
  address_t ret;
  asm volatile("xor    %%fs:0x30,%0\n"
               "rol    $0x11,%0\n"
      : "=g" (ret)
      : "0" (addr));
  return ret;
}

#else
/* code for 32 bit Intel arch */

typedef unsigned int address_t;
#define JB_SP 4
#define JB_PC 5


/* A translation is required when using an address of a variable.
   Use this as a black box in your code. */
address_t translate_address(address_t addr)
{
    address_t ret;
    asm volatile("xor    %%gs:0x18,%0\n"
                 "rol    $0x9,%0\n"
    : "=g" (ret)
    : "0" (addr));
    return ret;
}

#endif



namespace {

    typedef enum ThreadState {
        READY, RUNNING,BLOCKED,
    } ThreadState;

    typedef struct Thread
    {
        int tid, quantum;
        ThreadState state;
        char stack[STACK_SIZE];
        sigjmp_buf env;
    } Thread;

    // Fields //
    Thread *threads[MAX_THREAD_NUM]; // All existing threads.
    std::list<int> readyThreads;    // Ready threads list.
    // Threads map: tid -> (sleep, block).
    std::unordered_map<int, std::pair<int, bool>> blockedThreads;
    int running_tid, total_quantums;
    struct itimerval timer;
    int global_quantum_time;

    namespace thread_manager {
        void create_thread(int tid, thread_entry_point entry_point);
        void context_switch(bool terminate, ThreadState state);
        void terminate_thread(int tid);
        void block_thread(int tid);
        int get_available_tid();
        void mask_action(int how);
        int tid_validation(int tid);
        int quantum_validation(int quantum);
        void sig_handler(int sig);
    }

    namespace timer_manager {
        void set_timer(int quantum_usecs);
    }

    namespace thread_manager {

        // Initializes a new thread with a given ID and entry point function
        void create_thread(int tid, thread_entry_point entry_point) {
          threads[tid] = new Thread();
          threads[tid] -> tid = tid;
          threads[tid] -> state = READY;
          threads[tid] -> quantum = MIN_VALID_QUANTUM;
          sigsetjmp(threads[tid] -> env, 1);
          if (entry_point)
          {
            threads[tid] -> quantum--;
            auto sp = (address_t) (threads[tid] -> stack + STACK_SIZE -
                sizeof(address_t));
            auto pc = (address_t) entry_point;
            (threads[tid]->env->__jmpbuf)[JB_SP] = translate_address(sp);
            (threads[tid]->env->__jmpbuf)[JB_PC] = translate_address(pc);
            sigemptyset(&(threads[tid]->env->__saved_mask));
          }
        }

        // Saves the current thread’s context and switches to the next ready thread.
        void context_switch(bool terminate, ThreadState state)
        {
          thread_manager::mask_action (SIG_BLOCK);
          if (!terminate)
          {
            if (sigsetjmp(threads[running_tid]->env, 1) == 1)
            {
              thread_manager::mask_action (SIG_UNBLOCK);
              return;
            }
            else
            {
              threads[running_tid] -> state = state;
              //Update the running thread to be the next one in the ready list.
              if (state == READY)
              {
                readyThreads.push_back (running_tid);
              }
            }
          }
          running_tid = readyThreads.front();
          readyThreads.pop_front();
          threads[running_tid] -> state = RUNNING;
          threads[running_tid] -> quantum++;
          total_quantums++;
          timer_manager::set_timer(global_quantum_time);
          thread_manager::mask_action(SIG_UNBLOCK);
          siglongjmp(threads[running_tid]->env, 1);
        }

        // Deletes a thread by its ID and make a context switch if necessary.
        void terminate_thread(int tid) {
          ThreadState cur_state = threads[tid] -> state;
          delete threads[tid];
          threads[tid] = nullptr;
          switch(cur_state)
          {
            case READY:
              readyThreads.remove(tid);
              break;
            case BLOCKED:
              blockedThreads.erase(tid);
              break;
            case RUNNING:
              thread_manager::context_switch(true, READY);
              break;
            default:
              break;
          }
        }

        // Blocks a thread by its ID.
        void block_thread(int tid) {
          switch (threads[tid] -> state)
          {
            case READY:
              readyThreads.remove(tid);
              threads[tid] -> state = BLOCKED;
              blockedThreads[tid] = {0, true};
              break;

            case BLOCKED:
              blockedThreads[tid].second = true;
              break;

            case RUNNING:
              blockedThreads[tid] = {0, true};
              thread_manager::context_switch(false, BLOCKED);
              break;

            default:
              break;
          }
        }

        // Returns the smallest available thread ID (tid) that is not currently in use.
        int get_available_tid() {
          for (int i = 0; i < MAX_THREAD_NUM; ++i) {
            if (threads[i] == nullptr) {
              return i;
            }
          }
          return FAILED;
        }

        // Modifies the signal mask for the calling thread. It blocks or unblocks signals based on "how".
        void mask_action(int how) {
          sigset_t mask;
          sigemptyset (&mask);
          sigaddset (&mask, SIGVTALRM);
          if (sigprocmask(how, &mask, nullptr) == FAILED) // dis/activate mask
          {
            std::cerr<<SYSTEM_CALL_ERROR<<MASK_SIGNAL_MESSAGE(how)<<std::endl;
            exit( EXIT_FAIL);
          }
        }

        // Validates if a given tid is within valid range and if the corresponding thread exists.
        int tid_validation(int tid) {
          if(tid<MAIN_THREAD_TID||tid >=MAX_THREAD_NUM||threads[tid]==nullptr)
          {
            std::cerr << THREADS_LIBRARY_ERROR << THREAD_NULLPTR << std::endl;
            thread_manager::mask_action(SIG_UNBLOCK);
            return FAILED;
          }
          return GREAT_SUCCESS;
        }

        // Validates a given quantum value to ensure it’s not less than MIN_VALID_QAUNTUM (= 1).
        int quantum_validation(int quantum) {
          if (quantum< MIN_VALID_QUANTUM) {
            std::cerr<<THREADS_LIBRARY_ERROR<<NON_POSITIVE_USECS<<std::endl;
            thread_manager::mask_action(SIG_UNBLOCK);
            return FAILED;
          }
          return GREAT_SUCCESS;
        }

        // Signal handler function that is called when a SIGVTALRM signal is received, indicating that a quantum has expired.
        void sig_handler(int sig)
        {
            thread_manager::mask_action (SIG_BLOCK);

            // Handling sleeping threads
            std::vector<int> wakeup_threads;
            for (auto item : blockedThreads)
            {    // item  pair is <tid, <state, bool>>
                std::pair<int, bool> curr_restrictions = item.second;
                if (--curr_restrictions.first < MIN_VALID_QUANTUM &&
                    !curr_restrictions.second)
                {
                    threads[item.first] -> state = READY;
                    readyThreads.push_back(item.first);
                    wakeup_threads.push_back(item.first);
                }
            }
            // remove woken up threads from blocked
            for(auto tid : wakeup_threads)
            {
                blockedThreads.erase(tid);
            }
            thread_manager::context_switch (false, READY);
        }
    }

    namespace timer_manager {

        // Sets up a virtual timer that sends SIGVTALRM signals at intervals defined by quantum_usecs.
        void set_timer(int quantum_usecs)
        {
          struct sigaction sa = {0};
          sa.sa_handler = &thread_manager::sig_handler;
          if (sigaction(SIGVTALRM, &sa, nullptr) == FAILED) {
            std::cerr<<SYSTEM_CALL_ERROR<<SET_SIGNAL_HANDLER_FAILED<<std::endl;
            exit( EXIT_FAIL);
          }

          // Configure the timer to expire after quantum_usecs.
          timer.it_value.tv_usec = quantum_usecs;
          timer.it_value.tv_sec = 0;
          if (setitimer (ITIMER_VIRTUAL, &timer, nullptr))
          {
            std::cerr << SYSTEM_CALL_ERROR << SET_TIMER_FAILED << std::endl;
            exit(EXIT_FAIL);
          }
        }
    }
}


int uthread_init(int quantum_usecs)
{
  thread_manager::mask_action(SIG_BLOCK);

  if (thread_manager::quantum_validation(quantum_usecs) == FAILED)
  {
    return FAILED;
  }
  // Initialize the threads array to NULL.
  for (int i=1 ; i < MAX_THREAD_NUM ; i++)
  {
    threads[i] = nullptr;
  }

  global_quantum_time = quantum_usecs;
  // creates main thread (tid = 0)
  thread_manager::create_thread(MAIN_THREAD_TID, nullptr);
  total_quantums = MIN_VALID_QUANTUM;

  threads[MAIN_THREAD_TID] -> state = RUNNING;
  running_tid = MAIN_THREAD_TID;


  timer_manager::set_timer(quantum_usecs);

  thread_manager::mask_action(SIG_UNBLOCK);
  return GREAT_SUCCESS;
}


int uthread_spawn(thread_entry_point entry_point)
{
  thread_manager::mask_action(SIG_BLOCK);

  if (entry_point == nullptr)
  {
    std::cerr << THREADS_LIBRARY_ERROR << ENTRY_NULLPTR << std::endl;
    thread_manager::mask_action(SIG_UNBLOCK);
    return FAILED;
  }

  int tid = thread_manager::get_available_tid();
  if (tid == FAILED)
  {
    std::cerr << THREADS_LIBRARY_ERROR << MAX_THREADS_REACHED << std::endl;
    thread_manager::mask_action(SIG_UNBLOCK);
    return FAILED;
  }

  thread_manager::create_thread(tid, entry_point);
  readyThreads.push_back(tid);

  thread_manager::mask_action(SIG_UNBLOCK);
  return tid;
}


int uthread_terminate(int tid)
{
  thread_manager::mask_action(SIG_BLOCK);
  if (thread_manager::tid_validation(tid) == FAILED)
  {
    return FAILED;
  }

  if (tid == MAIN_THREAD_TID)
  {
    for (int i = 0 ; i < MAX_THREAD_NUM ; i++)
    {
      delete threads[i];
      threads[i] = nullptr;
    }
    exit(GREAT_SUCCESS);
  }

  thread_manager::terminate_thread(tid);
  thread_manager::mask_action(SIG_UNBLOCK);
  return GREAT_SUCCESS;
}


int uthread_block(int tid)
{
  thread_manager::mask_action(SIG_BLOCK);
  if (thread_manager::tid_validation(tid) == FAILED)
  {
    return FAILED;
  }

  if (tid == MAIN_THREAD_TID)
  {
    std::cerr << THREADS_LIBRARY_ERROR << BLOCK_MAIN_THREAD << std::endl;
    thread_manager::mask_action(SIG_UNBLOCK);
    return FAILED;
  }

  thread_manager::block_thread(tid);
  thread_manager::mask_action(SIG_UNBLOCK);
  return GREAT_SUCCESS;
}


int uthread_resume(int tid)
{
  thread_manager::mask_action(SIG_BLOCK);
  if (thread_manager::tid_validation(tid) == FAILED)
  {
    return FAILED;
  }

  if (blockedThreads[tid].first < MIN_VALID_QUANTUM)
  {
    blockedThreads.erase(tid);
    readyThreads.push_back(tid);
    threads[tid] -> state = READY;
  }
  else
  {
    blockedThreads[tid].second = false;
  }

  thread_manager::mask_action(SIG_UNBLOCK);
  return GREAT_SUCCESS;
}


int uthread_sleep(int num_quantums)
{
  thread_manager::mask_action(SIG_BLOCK);

  if (thread_manager::quantum_validation(num_quantums))
  {
    return FAILED;
  }

  if (running_tid == MAIN_THREAD_TID)
  {
    std::cerr << THREADS_LIBRARY_ERROR << SLEEP_MAIN_THREAD << std::endl;
    thread_manager::mask_action(SIG_UNBLOCK);
    return FAILED;
  }
  // maybe num_quantums + 1 - TODO ?
  blockedThreads[running_tid] = {num_quantums, false};
  thread_manager::context_switch(false, BLOCKED);

  thread_manager::mask_action(SIG_UNBLOCK);
  return GREAT_SUCCESS;
}


int uthread_get_tid()
{
  return running_tid;
}


int uthread_get_total_quantums()
{
  return total_quantums;
}


int uthread_get_quantums(int tid)
{
  if (thread_manager::tid_validation(tid) == FAILED)
  {
    return FAILED;
  }
  return threads[tid] -> quantum;
}
