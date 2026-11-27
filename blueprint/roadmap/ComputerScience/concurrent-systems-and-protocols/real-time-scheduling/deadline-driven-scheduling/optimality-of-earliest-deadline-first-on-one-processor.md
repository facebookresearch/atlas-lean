# Optimality of earliest-deadline-first scheduling on one processor

Let $J_1, \dots, J_n$ be finitely many independent jobs with arbitrary release times, execution requirements and deadlines, to be scheduled preemptively on one processor. If the set of jobs is feasible, then every [earliest-deadline-first schedule](earliest-deadline-first-schedules.md) of it is feasible, whatever rule breaks ties between equal deadlines. The jobs need not come from periodic tasks; when they do, relative deadlines may be shorter than, equal to or longer than the periods.

**Proof idea.** Start from a feasible schedule. Whenever a piece of job $J_i$ runs at a time at which an active job $J_k$ with $d_k < d_i$ also has work left that the schedule performs later, exchange equal amounts of the two jobs' execution; both still complete by their deadlines, since the exchanged work of $J_i$ now finishes no later than $J_k$ finished before and $d_k < d_i$. Repeating removes every violation of the EDF order, and moving work into idle intervals during which some job is active yields an EDF schedule that is still feasible. Since any two EDF schedules differ only in the order of jobs with equal deadlines, all of them are feasible.

## Depends on

- [Preemptive schedules of jobs on one processor](preemptive-schedules-of-jobs-on-one-processor.md)
- [Earliest-deadline-first schedules](earliest-deadline-first-schedules.md)

## Sources

- M. Sojka, *Deadline-driven scheduling*, lecture slides for Real-Time Systems, Czech Technical University in Prague, 22 November 2023, <https://rtime.felk.cvut.cz/psr/prednasky/3/03-rts.pdf>, slide 7 (the theorem: when preemption is allowed and jobs do not contend for resources, EDF produces a feasible schedule of a set of independent jobs with arbitrary release times and deadlines on a processor if and only if the set has feasible schedules) and slides 8–9 (the exchange proof).
- R. I. Davis and A. Burns, "A survey of hard real-time scheduling for multiprocessor systems", *ACM Computing Surveys* 43(4), article 35, 2011; author version <https://www-users.york.ac.uk/~rd17/papers/MPSurveyv4.9.pdf>, Section 5: EDF is the optimal pre-emptive uniprocessor scheduling algorithm for sporadic task sets whatever their deadline constraints, a result attributed there to Dertouzos (1974).
