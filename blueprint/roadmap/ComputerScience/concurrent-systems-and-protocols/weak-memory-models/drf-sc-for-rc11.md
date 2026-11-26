# Data-race freedom guarantees sequential consistency under RC11

An execution is *SC-consistent* if it is complete, satisfies atomicity ($\mathtt{rmw} \cap (\mathtt{rb} ; \mathtt{mo}) = \emptyset$), and $\mathtt{sb} \cup \mathtt{rf} \cup \mathtt{mo} \cup \mathtt{rb}$ is acyclic. The outcomes of a program $P$ under sequential consistency are the outcomes of its SC-consistent full executions. If in every SC-consistent execution of $P$ every race $(a, b)$ has both $a$ and $b$ of mode $sc$, then the [outcomes of $P$ under RC11](rc11-program-outcomes.md) coincide with its outcomes under sequential consistency. The no-thin-air condition of [RC11 consistency](rc11-consistent-executions.md) is needed for this.

## Depends on

- [Outcomes of a program under RC11](rc11-program-outcomes.md)
- [RC11-consistent executions](rc11-consistent-executions.md)

## Sources

- O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer, "Repairing sequential consistency in C/C++11", *Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017)*, 2017, <https://plv.mpi-sws.org/scfix/paper.pdf>, Section 8 ("Programming guarantees"): the declarative definition of SC-consistency and Theorem 4, with the remark that the no-thin-air condition is essential.
