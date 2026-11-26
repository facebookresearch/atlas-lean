# The critical instant theorem

In the Liu–Layland periodic task model (over intervals in which no non-periodic routine runs), the *response time* of a request is the time from the request to the end of the response to it, and a *critical instant* of a task is an instant at which a request for it has the largest response time that a request for it can have, whatever the phases of the tasks. Under a preemptive fixed-priority scheduling algorithm, a critical instant for any task occurs whenever the task is requested simultaneously with requests for all higher-priority tasks. Consequently, if, when all tasks are first requested at time $0$, the first request of every task is fulfilled before its deadline, the priority assignment is feasible whatever the phases of the tasks.

## Depends on

- [The Liu–Layland periodic task model](the-liu-layland-periodic-task-model.md)

## Sources

- C. L. Liu and J. W. Layland, "Scheduling algorithms for multiprogramming in a hard-real-time environment", *Journal of the ACM* 20(1):46–61, 1973, Section 4, the definitions of response time and critical instant, Theorem 1 and the remark following it
