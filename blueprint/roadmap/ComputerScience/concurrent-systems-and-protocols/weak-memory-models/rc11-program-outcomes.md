# Outcomes of a program under RC11

Two events $a \ne b$ of an execution are *conflicting* if they access the same location and at least one is a write. A conflicting pair is a *race* if neither $(a, b)$ nor $(b, a)$ is in happens-before $\mathtt{hb}$. An execution is *racy* if it has a race in which at least one event is non-atomic (mode $na$), and a program has *undefined behaviour* under RC11 if one of its executions, full or not, is [RC11-consistent](rc11-consistent-executions.md) and racy. The *outcome* of an execution is the function assigning to each location the value written by its $\mathtt{mo}$-maximal write. A function $O$ from locations to values is an *outcome of a program $P$ under RC11* if either $O$ is the outcome of some RC11-consistent full execution of $P$, or $P$ has undefined behaviour under RC11, in which case every $O$ is an outcome.

## Depends on

- [RC11-consistent executions](rc11-consistent-executions.md)

## Sources

- O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer, "Repairing sequential consistency in C/C++11", *Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017)*, 2017, <https://plv.mpi-sws.org/scfix/paper.pdf>, Section 3.3 ("Program outcomes"): Definitions 2, 3 and 4.
