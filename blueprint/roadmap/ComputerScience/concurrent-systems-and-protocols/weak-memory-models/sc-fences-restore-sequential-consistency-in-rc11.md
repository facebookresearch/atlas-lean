# SC fences between shared accesses restore sequential consistency in RC11

A location $x$ is *shared* in an execution if two distinct accesses to $x$ are unrelated by $\mathtt{sb}$ in both directions. Let $G$ be an [RC11-consistent execution](rc11-consistent-executions.md). If for every two distinct shared locations $x$ and $y$ every $\mathtt{sb}$-edge from an access to $x$ to an access to $y$ passes through an SC fence, that is $[\mathtt{E}_x] ; \mathtt{sb} ; [\mathtt{E}_y] \subseteq \mathtt{sb} ; [\mathtt{F}^{sc}] ; \mathtt{sb}$, then $G$ is SC-consistent: it is complete, satisfies atomicity, and $\mathtt{sb} \cup \mathtt{rf} \cup \mathtt{mo} \cup \mathtt{rb}$ is acyclic.

## Depends on

- [RC11-consistent executions](rc11-consistent-executions.md)

## Sources

- O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer, "Repairing sequential consistency in C/C++11", *Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017)*, 2017, <https://plv.mpi-sws.org/scfix/paper.pdf>, Section 8: Definition 7 and Theorem 5.
