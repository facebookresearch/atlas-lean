# Constrained-deadline sporadic tasks

A *sporadic task* $\tau_i = (C_i, T_i, D_i)$ on one processor makes a sequence of requests (jobs) whose release times are separated by at least $T_i > 0$; each job needs at most $C_i \ge 0$ units of processor time and must complete within $D_i > 0$ of its release. The task has a *constrained deadline* if $D_i \le T_i$, and an *implicit deadline* if $D_i = T_i$; a periodic task has releases exactly $T_i$ apart, so that the tasks of the [Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md) are periodic tasks with implicit deadlines. Tasks are independent and every job is ready for execution at its release (no release jitter).

Under *preemptive fixed-priority scheduling* each task has a distinct static priority shared by all its jobs, and at every time the processor executes the active job of highest priority. The *response time* of a job is the time from its release to its completion, and the *worst-case response time* $R_i$ of $\tau_i$ is the supremum of the response times of its jobs over all release sequences respecting the minimum separations and all execution times in $[0, C_i]$. A task set is *schedulable* under a priority assignment if $R_i \le D_i$ for every task. The *deadline-monotonic* priority assignment gives higher priority to tasks with shorter relative deadlines.

## Depends on

- [The Liu–Layland periodic task model](../the-liu-layland-periodic-task-model.md)

## Sources

- N. Audsley, A. Burns, M. Richardson, K. Tindell and A. J. Wellings, "Applying new scheduling theory to static priority pre-emptive scheduling", *Software Engineering Journal* 8(5), 1993; author version <https://www.math.unipd.it/~tullio/RTS/2009/ABRTW-1993.pdf>, Section 2 (the computational model: minimum inter-arrival time $T_i$, bounded computation $C_i$, deadlines relative to release, static base priorities) and the glossary of Section 3 (with $D_i \le T_i$ required).
- R. I. Davis and A. Burns, "A survey of hard real-time scheduling for multiprocessor systems", *ACM Computing Surveys* 43(4), article 35, 2011; author version <https://www-users.york.ac.uk/~rd17/papers/MPSurveyv4.9.pdf>, Section 2.2 (periodic and sporadic task models with implicit, constrained and arbitrary deadlines).
