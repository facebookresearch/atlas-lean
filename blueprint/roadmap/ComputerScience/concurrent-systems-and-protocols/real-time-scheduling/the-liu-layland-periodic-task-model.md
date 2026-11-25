# The Liu–Layland periodic task model

A *hard-real-time task system* in the sense of Liu and Layland consists of tasks $\tau_1, \dots, \tau_m$ on one processor satisfying the following assumptions:

1. the requests for each task are periodic, with a constant interval $T_i$, the *request period*, between successive requests;
2. each request must be completed before the next request for the same task occurs;
3. the tasks are independent: requests for one task do not depend on the initiation or completion of requests for other tasks;
4. the *run-time* $C_i$ of each task, the processor time it takes to execute the task without interruption, is constant;
5. any non-periodic tasks are initialization or failure-recovery routines without hard deadlines, which displace the periodic tasks while they run.

The results stated for this model concern the periodic tasks over intervals in which no non-periodic routine runs; the analyzed task system consists of the periodic tasks alone.

A task is thus characterized by its request period $T_i$ and its run-time $C_i$; its *request rate* is $1/T_i$. A *scheduling algorithm* determines the task executed at each moment. It is *preemptive and priority driven* if, whenever a task of higher priority than the running one is requested, the running task is immediately interrupted and the requested task started, and *static* (fixed priority) if priorities are assigned to tasks once and for all. The *deadline* of a request is the time of the next request for the same task; an *overflow* occurs at time $t$ if $t$ is the deadline of an unfulfilled request; and a scheduling algorithm is *feasible* for a task set if no overflow ever occurs. The *response time* of a request is the time from the request to the end of the response to it, and a *critical instant* of a task is an instant at which a request for it has the largest response time.

## Sources

- C. L. Liu and J. W. Layland, "Scheduling algorithms for multiprogramming in a hard-real-time environment", *Journal of the ACM* 20(1):46–61, 1973, Sections 3 and 4
