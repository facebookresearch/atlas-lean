# RC11 without mixed SC accesses gives the C11 guarantee

Let $G$ be an execution as in [RC11-consistent executions](rc11-consistent-executions.md) in which SC accesses are to distinguished locations: for all events $a, b$ other than the initialization writes, if $a$ has mode $sc$ and accesses the same location as $b$, then $b$ has mode $sc$. Then $[E^{sc}] ; \mathtt{hb} ; [E^{sc}] \subseteq \mathtt{psc}^+$.

## Depends on

- [RC11-consistent executions](rc11-consistent-executions.md)

## Sources

- O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer, "Repairing sequential consistency in C/C++11", *Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017)*, 2017, <https://plv.mpi-sws.org/scfix/paper.pdf>, Section 3.2 (consistency) and Section 3.4 ("Comparison with C11"), Proposition 3 and the paragraph before it.
