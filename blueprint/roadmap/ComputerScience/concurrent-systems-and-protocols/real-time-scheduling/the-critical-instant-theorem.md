# The critical instant theorem

In the Liu–Layland periodic task model (over intervals in which no non-periodic routine runs), consider the [preemptive priority-driven schedules](produce-schedule.md) of a [fixed-priority rule](is-fixed-priority.md), with ties between equal priorities broken by task index as in these schedules, for tasks of given run-times and request periods, under every choice of their phases for which no request of a task of higher priority than $\tau_i$ overflows. A *critical instant* of $\tau_i$ is an instant at which a request for $\tau_i$ has the largest [response time](response-time.md) that a request for $\tau_i$ has in these schedules, a request that is never fulfilled counting as having a larger response time than every fulfilled one. A critical instant for $\tau_i$ occurs whenever $\tau_i$ is requested simultaneously with requests for all higher-priority tasks.

Consequently, if, when all tasks are first requested at time $0$, the first request of every task is fulfilled before its deadline, the priority rule is feasible whatever the phases of the tasks.

The phases under which a higher-priority request overflows are left out because such a request is dropped at its deadline, which can leave more processor time to $\tau_i$. For instance, with the tasks $(C, T, \varphi) = (2, 5, 0), (1, 2, 0), (1, 5, 0)$ in decreasing priority, the first request of the second task overflows, and the third task has response time $4$ for its request at time $0$, made together with requests for both higher-priority tasks, but $5$ for its request at time $5$.

## Depends on

- [The Liu–Layland periodic task model](the-liu-layland-periodic-task-model.md)
- [Preemptive priority-driven schedules](produce-schedule.md)
- [Fixed-priority rules](is-fixed-priority.md)
- [Response time of a request](response-time.md)

## Sources

- C. L. Liu and J. W. Layland, "Scheduling algorithms for multiprogramming in a hard-real-time environment", *Journal of the ACM* 20(1):46–61, 1973, Section 4, the definitions of response time and critical instant, Theorem 1 and the remark following it
