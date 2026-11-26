# The Liu–Layland periodic task model

A *hard-real-time task system* in the sense of Liu and Layland consists of tasks $\tau_i$, indexed by a finite set, on one processor satisfying the following assumptions:

1. the requests for each task are periodic, with a constant interval $T_i$, the *request period*, between successive requests;
2. each request must be completed before the next request for the same task occurs;
3. the tasks are independent: requests for one task do not depend on the initiation or completion of requests for other tasks;
4. the *run-time* $C_i$ of each task, the processor time it takes to execute the task without interruption, is constant;
5. any non-periodic tasks are initialization or failure-recovery routines without hard deadlines, which displace the periodic tasks while they run.

The results stated for this model concern the periodic tasks over intervals in which no non-periodic routine runs; the analyzed task system consists of the periodic tasks alone.

Time is discrete here, whereas Liu and Layland take it to be continuous: the slot $t \in \mathbb{N}$ is the interval $[t, t + 1)$, and run-times, request periods and request times are natural numbers. A task $\tau_i$ is given by its run-time $C_i \ge 1$, its request period $T_i \ge 1$ and its *phase* $\varphi_i$, the time of its first request: its requests are made at the times $\varphi_i + kT_i$ for $k = 0, 1, 2, \dots$. Liu and Layland characterize a task by $T_i$ and $C_i$ alone, and call $1/T_i$ its *request rate*; the phase records when its requests start, which their assumptions leave free. The run-time may exceed the request period, although then [no schedule is feasible](run-time-le-period.md).

A *schedule* assigns to each slot the task executed in it, if any. The *deadline* of a request is the time of the next request for the same task: the request of $\tau_i$ made at $\varphi_i + kT_i$ has deadline $\varphi_i + (k + 1)T_i$. A request is *fulfilled* if the schedule executes its task in at least $C_i$ of the slots from the request up to its deadline. An *overflow* occurs at time $t$ if $t$ is the deadline of an unfulfilled request, and a schedule is *feasible* if no overflow ever occurs, that is, if every request is fulfilled. A *scheduling algorithm* determines the task executed at each moment, and so a schedule for each task set; it is *feasible* for a task set if its schedule for that task set is feasible.

A scheduling algorithm is *preemptive and priority driven* if, whenever a task of higher priority than the running one is requested, the running task is immediately interrupted and the requested task started. Such an algorithm is given by a *priority rule*, which assigns to each request of each task a priority in a linearly ordered set, a smaller value meaning a higher priority. A request is *pending* in a slot if it has been made, its deadline has not passed and it is not yet fulfilled, its task having run in fewer than $C_i$ of the slots since the request; so a request whose deadline passes unfulfilled stops being pending. In each slot, the schedule of the algorithm executes the task of the pending request of highest priority, ties being broken by a fixed order of the tasks, and it leaves the processor idle only when no request is pending. The algorithm is *static* (fixed priority) if all requests of each task have the same priority.

## Sources

- C. L. Liu and J. W. Layland, "Scheduling algorithms for multiprogramming in a hard-real-time environment", *Journal of the ACM* 20(1):46–61, 1973, Sections 3 and 4
