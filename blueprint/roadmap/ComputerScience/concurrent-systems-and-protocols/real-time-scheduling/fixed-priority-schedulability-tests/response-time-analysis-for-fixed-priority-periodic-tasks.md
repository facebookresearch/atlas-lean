# Response-time analysis for fixed-priority periodic tasks

Consider tasks $\tau_1, \dots, \tau_m$ of the [Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md), with periods $T_j > 0$ and run-times $C_j > 0$, scheduled by the [preemptive priority-driven schedules](../periodic-task-model/produce-schedule.md) of a [fixed-priority rule](../periodic-task-model/is-fixed-priority.md) in which every task has its own priority, and let $hp(i)$ be the set of tasks of higher priority than $\tau_i$. For $r > 0$ put

$$
W_i(r) = C_i + \sum_{j \in hp(i)} \left\lceil \frac{r}{T_j} \right\rceil C_j .
$$

Then the priority assignment is feasible whatever the phases if and only if, for every task $\tau_i$, $W_i(r) = r$ for some $r \in (0, T_i]$. In that case the largest [response time](../periodic-task-model/response-time.md) of a request of $\tau_i$, over all phases, is the least $r > 0$ with $W_i(r) = r$.

The criterion is stated for the whole task set: for a single task it can fail here, since a request that is not fulfilled by its deadline is dropped. With $(C, T) = (2, 5), (1, 2), (1, 6)$ in decreasing priority, no request of the third task overflows, whatever the phases, although $W_3(5) = 6$ and $W_3(6) = 8$, so that $W_3$ has no fixed point in $(0, 6]$; the requests of the second task can overflow, as $W_2$ has no fixed point in $(0, 2]$.

The fixed-point equation describes a request of $\tau_i$ made at a critical instant: in a window of length $r$ starting at that instant, each higher-priority task $\tau_j$ makes $\lceil r/T_j \rceil$ requests, each of which preempts $\tau_i$ for $C_j$. When the priority assignment is feasible whatever the phases, the request of $\tau_i$ completes at the least positive fixed point $r \le T_i$, the first time by which all this work, together with its own $C_i$, has been done. A fixed point above $T_i$ is no completion time: with the tasks $(C, T) = (2, 3), (2, 4)$ in decreasing priority, first requested together, the first task never overflows, the least fixed point of $W_2$ is $6$, and the first request of the second task is dropped at time $4$ with no response time.

## Depends on

- [The Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md)
- [Preemptive priority-driven schedules](../periodic-task-model/produce-schedule.md)
- [Fixed-priority rules](../periodic-task-model/is-fixed-priority.md)
- [Response time of a request](../periodic-task-model/response-time.md)

## Proof depends on

- [The critical instant theorem](../the-critical-instant-theorem.md): when the priority assignment is feasible whatever the phases, the largest response time of $\tau_i$ occurs for a request made together with requests of all higher-priority tasks; and, by Liu and Layland's remark following it, feasibility whatever the phases follows once the first request of every task is fulfilled when all tasks are first requested at time $0$.

## Sources

- N. Audsley, A. Burns, M. Richardson, K. Tindell and A. J. Wellings, "Applying new scheduling theory to static priority pre-emptive scheduling", *Software Engineering Journal* 8(5), 1993; author version <https://www.math.unipd.it/~tullio/RTS/2009/ABRTW-1993.pdf>, Section 3: the interference bound $\lceil r_i/T_j\rceil C_j$ of each higher-priority task, equations (1)–(2) for the worst-case response time and the requirement $r_i \le D_i$, here with $D_i = T_i$, no blocking ($B_i = 0$) and no release jitter; the analysis is credited there to M. Joseph and P. Pandya, "Finding response times in a real-time system", *The Computer Journal* 29(5):390–395, 1986.
- R. Bettati, *CPSC 663: Real-Time Systems*, Texas A&M University, lecture slides "Priority Driven Scheduling", 2016, <https://people.engr.tamu.edu/bettati/Courses/663/2016C/Slides/priority_driven.pdf>, p. 13 (the time-demand equation for the response time of the job released at a critical instant) and p. 16 (time-demand analysis: that job "meets its deadline if, for some $t_1 \le D_i \le p_i$: $w_i(t_1) \le t_1$", and if this does not hold, the "system of tasks is not schedulable by given static-priority algorithm")
