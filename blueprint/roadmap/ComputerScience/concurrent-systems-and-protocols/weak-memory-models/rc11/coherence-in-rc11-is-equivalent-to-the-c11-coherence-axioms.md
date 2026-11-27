# RC11 coherence is equivalent to the C11 coherence axioms

For an execution $G$ as in [RC11-consistent executions](rc11-consistent-executions.md), the coherence condition, that $\mathtt{hb} ; \mathtt{eco}^?$ is irreflexive, holds if and only if all of the following relations are irreflexive: $\mathtt{hb}$; $\mathtt{rf} ; \mathtt{hb}$; $\mathtt{mo} ; \mathtt{rf} ; \mathtt{hb}$; $\mathtt{mo} ; \mathtt{hb}$; $\mathtt{mo} ; \mathtt{hb} ; \mathtt{rf}^{-1}$; and $\mathtt{mo} ; \mathtt{rf} ; \mathtt{hb} ; \mathtt{rf}^{-1}$.

## Depends on

- [RC11-consistent executions](rc11-consistent-executions.md)

## Sources

- O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer, "Repairing sequential consistency in C/C++11", *Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017)*, 2017, <https://plv.mpi-sws.org/scfix/paper.pdf>, Section 3.2 (consistency) and Section 3.4 ("Comparison with C11"), Proposition 1 (the constraints IRREFLEXIVE-HB, NO-FUTURE-READ, COHERENCE-RW, COHERENCE-WW, COHERENCE-WR and COHERENCE-RR of C11).
