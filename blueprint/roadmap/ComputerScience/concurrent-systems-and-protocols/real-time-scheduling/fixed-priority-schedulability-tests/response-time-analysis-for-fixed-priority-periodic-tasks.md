# Response-time analysis for fixed-priority periodic tasks

Consider tasks $\tau_1, \dots, \tau_m$ of the [Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md), with periods $T_j > 0$ and run-times $C_j > 0$, scheduled by the [preemptive priority-driven schedules](../produce-schedule.md) of a [fixed-priority rule](../is-fixed-priority.md) in which every task has its own priority, and let $hp(i)$ be the set of tasks of higher priority than $\tau_i$. For $r > 0$ put

$$
W_i(r) = C_i + \sum_{j \in hp(i)} \left\lceil \frac{r}{T_j} \right\rceil C_j .
$$

Suppose that no request of a task in $hp(i)$ overflows, whatever the phases of the tasks. Then no request of $\tau_i$ overflows, whatever the phases, if and only if $W_i(r) = r$ for some $r \in (0, T_i]$; in that case the largest [response time](../response-time.md) of a request of $\tau_i$, over all phases, is the least $r > 0$ with $W_i(r) = r$. The priority assignment is feasible whatever the phases exactly when, for every task $\tau_j$, $W_j(r) = r$ for some $r \in (0, T_j]$.

The hypothesis on the tasks in $hp(i)$ is needed because a request that is not fulfilled by its deadline is dropped: with $(C, T) = (2, 5), (1, 2), (1, 6)$ in decreasing priority, no request of the third task overflows, whatever the phases, although $W_3(5) = 6$ and $W_3(6) = 8$, so that $W_3$ has no fixed point in $(0, 6]$; the requests of the second task can overflow.

The fixed-point equation describes a request of $\tau_i$ made at a critical instant: in a window of length $r$ starting at that instant, each higher-priority task $\tau_j$ makes $\lceil r/T_j \rceil$ requests, each of which preempts $\tau_i$ for $C_j$, and the request of $\tau_i$ completes at the first time $r$ by which all this work, together with its own $C_i$, has been done.

## Depends on

- [The Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md)
- [Preemptive priority-driven schedules](../produce-schedule.md)
- [Fixed-priority rules](../is-fixed-priority.md)
- [Response time of a request](../response-time.md)

## Proof depends on

- [The critical instant theorem](../the-critical-instant-theorem.md): when no request of a higher-priority task overflows, the largest response time of $\tau_i$ occurs for a request made together with requests of all higher-priority tasks.

## Sources

- N. Audsley, A. Burns, M. Richardson, K. Tindell and A. J. Wellings, "Applying new scheduling theory to static priority pre-emptive scheduling", *Software Engineering Journal* 8(5), 1993; author version <https://www.math.unipd.it/~tullio/RTS/2009/ABRTW-1993.pdf>, Section 3: the interference bound $\lceil r_i/T_j\rceil C_j$ of each higher-priority task, equations (1)–(2) for the worst-case response time and the requirement $r_i \le D_i$, here with $D_i = T_i$, no blocking ($B_i = 0$) and no release jitter; the analysis is credited there to M. Joseph and P. Pandya, "Finding response times in a real-time system", *The Computer Journal* 29(5):390–395, 1986.
