# Shortest processing time first minimizes total completion time

For jobs with processing times $p_1, \dots, p_n$, all released at time $0$, on a single machine without preemption, scheduling the jobs in nondecreasing order of processing time minimizes the total completion time $\sum_j C_j$. The proof is an exchange argument: in any schedule, swapping two adjacent jobs that appear in decreasing order of processing time does not increase the total, and repeated swaps reach the nondecreasing order.

## Expansion

This page becomes ready once these prerequisites are stated:

- Single-machine nonpreemptive schedules and their completion times (statement prerequisite)

## Sources

- C. Stein (instructor) and N. Mohan (scribe), "Lecture 8: Sum of completion times with release dates", IEOR 8100 Scheduling Algorithms lecture notes, Columbia University, 2016, Section 1, the optimality of shortest processing time first for $1 \| \sum_j C_j$, <https://www1.columbia.edu/~cs2035/courses/ieor8100.F16/lec8.pdf>
- W. E. Smith, "Various optimizers for single-stage production", *Naval Research Logistics Quarterly* 3(1–2):59–66, 1956
- M. L. Pinedo, *Scheduling: Theory, Algorithms, and Systems*, 5th ed., Springer, 2016
