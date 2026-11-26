# Earliest-deadline-first schedules

A [preemptive schedule](preemptive-schedules-of-jobs-on-one-processor.md) $\sigma$ of the jobs $J_1, \dots, J_n$ on one processor is an *earliest-deadline-first* (EDF) schedule if, for almost every time $t$, whenever some job is active at $t$, the job executed at $t$ is an active job whose deadline is the least among the deadlines of the active jobs; ties between equal deadlines are broken arbitrarily. In particular an EDF schedule is work-conserving: the processor is idle only when no job is active. Applied to the jobs of periodic tasks, with the deadline of a request at the next request of the same task, this is the deadline-driven algorithm of Liu and Layland.

## Depends on

- [Preemptive schedules of jobs on one processor](preemptive-schedules-of-jobs-on-one-processor.md)

## Sources

- M. Sojka, *Deadline-driven scheduling*, lecture slides for Real-Time Systems, Czech Technical University in Prague, 22 November 2023, <https://rtime.felk.cvut.cz/psr/prednasky/3/03-rts.pdf>, slide 6: the scheduler selects a job with the earliest deadline.
