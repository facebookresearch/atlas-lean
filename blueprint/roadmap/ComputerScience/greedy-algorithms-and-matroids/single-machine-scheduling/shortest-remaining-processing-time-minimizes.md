# Shortest remaining processing time minimizes total flow time

For jobs with release times and processing times on a single machine with preemption allowed, the shortest-remaining-processing-time rule, which at every moment runs a released unfinished job with the least remaining processing time, minimizes the total flow time $\sum_j (C_j - r_j)$. Since $\sum_j r_j$ does not depend on the schedule, this is the same as minimizing the total completion time $\sum_j C_j$.

## Expansion

This page becomes ready once these prerequisites are stated:

- Single-machine preemptive schedules with release times and their completion times (statement prerequisite)

## Sources

- C. Stein (instructor) and N. Mohan (scribe), "Lecture 8: Sum of completion times with release dates", IEOR 8100 Scheduling Algorithms lecture notes, Columbia University, 2016, Section 3, the optimality of shortest remaining processing time for $1 \mid \mathrm{pmtn}, r_j \mid \sum_j C_j$, <https://www1.columbia.edu/~cs2035/courses/ieor8100.F16/lec8.pdf>
- L. Schrage, "A proof of the optimality of the shortest remaining processing time discipline", *Operations Research* 16(3):687–690, 1968
