# The RC11 SC condition as a total order on SC events

For an execution $G$ as in [RC11-consistent executions](rc11-consistent-executions.md) with set $E^{sc}$ of events of mode $sc$, the SC condition, that $\mathtt{psc}$ is acyclic, holds if and only if there is a strict total order $S$ on $E^{sc}$ such that $S ; \mathtt{psc}$ is irreflexive.

## Depends on

- [RC11-consistent executions](rc11-consistent-executions.md)

## Sources

- O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer, "Repairing sequential consistency in C/C++11", *Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017)*, 2017, <https://plv.mpi-sws.org/scfix/paper.pdf>, Section 3.2, Proposition 2.
