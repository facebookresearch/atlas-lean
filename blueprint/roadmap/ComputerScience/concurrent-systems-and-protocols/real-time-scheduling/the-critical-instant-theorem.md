# The critical instant theorem

In the Liu–Layland periodic task model (over intervals in which no non-periodic routine runs), consider the [preemptive priority-driven schedules](produce-schedule.md) of a [fixed-priority rule](is-fixed-priority.md), which order the tasks by priority, ties broken by task index, for tasks of given run-times and request periods, under every choice of their phases, and suppose that in each of these schedules every request is fulfilled before the next request of the same task, that is, by its deadline: the priority rule is feasible whatever the phases. A *critical instant* of $\tau_i$ is an instant at which a request for $\tau_i$ has the largest [response time](response-time.md) that a request for $\tau_i$ has in these schedules. A critical instant for $\tau_i$ occurs whenever $\tau_i$ is requested simultaneously with requests for all tasks that precede $\tau_i$ in this order.

Liu and Layland's remark following the theorem needs no such hypothesis: if, when all tasks are first requested at time $0$, the first request of every task is fulfilled by its deadline, the priority rule is feasible whatever the phases of the tasks. The remark concerns overflows alone, and a schedule up to its first overflow does not depend on what becomes of a request once it overflows.

The hypothesis of the theorem is needed because a request that is not fulfilled by its deadline is dropped, which can leave more processor time to later requests: with the tasks $(C, T, \varphi) = (2, 5, 0), (1, 2, 0), (1, 5, 0)$ in this order, the first request of the second task overflows, and the third task has response time $4$ for its request at time $0$, made together with requests for both tasks preceding it, but $5$ for its request at time $5$. It is asked whatever the phases, rather than only for the phases at hand, so that the phases at which $\tau_i$ is requested together with all preceding tasks are among those considered: with $(3, 6, 0), (1, 3, 1), (1, 6, 5)$ no request overflows, but every phasing at which the first two tasks are requested together makes the second overflow.

## Depends on

- [The Liu–Layland periodic task model](the-liu-layland-periodic-task-model.md)
- [Preemptive priority-driven schedules](produce-schedule.md)
- [Fixed-priority rules](is-fixed-priority.md)
- [Response time of a request](response-time.md)

## Sources

- C. L. Liu and J. W. Layland, "Scheduling algorithms for multiprogramming in a hard-real-time environment", *Journal of the ACM* 20(1):46–61, 1973, Section 4, the definitions of response time and critical instant, Theorem 1 and the remark following it
- R. Bettati, *CPSC 663: Real-Time Systems*, Texas A&M University, lecture slides "Priority Driven Scheduling", 2016, <https://people.engr.tamu.edu/bettati/Courses/663/2016C/Slides/priority_driven.pdf>, p. 12: the definition of a critical instant and the theorem that "in a fixed-priority system where every job completes before the next job in the same task is released, a critical instant of a task $T_i$ occurs when one of its jobs $J_{i,c}$ is released at the same time with a job of every higher-priority task"
