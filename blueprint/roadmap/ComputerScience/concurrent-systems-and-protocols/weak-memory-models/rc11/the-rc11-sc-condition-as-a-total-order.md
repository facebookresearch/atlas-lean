# The RC11 SC condition as a total order on SC events

For an execution $G$ as in [RC11-consistent executions](rc11-consistent-executions.md) with set $E^{sc}$ of events of mode $sc$, the SC condition, that $\mathtt{psc}$ is acyclic, holds if and only if there is a strict total order $S$ on $E^{sc}$ that extends $\mathtt{psc}$, that is, with $\mathtt{psc} \subseteq S$; equivalently, if and only if $\mathtt{psc}$ is irreflexive and $S ; \mathtt{psc}$ is irreflexive for some strict total order $S$ on $E^{sc}$. The source states the shorter test, irreflexivity of $S ; \mathtt{psc}$ alone, for executions that also satisfy the coherence condition of RC11 consistency ($\mathtt{hb} ; \mathtt{eco}^?$ irreflexive), which makes $\mathtt{psc}$ irreflexive. Without it the shorter test is too weak: in one thread with relaxed writes $w_1$ and $w_2$ to one location and an SC fence $f$, $w_1 \mathrel{\mathtt{sb}} f \mathrel{\mathtt{sb}} w_2$, and $w_2 \mathrel{\mathtt{mo}} w_1$, the pair $(f, f)$ is in $\mathtt{psc}_F$, while $f$ is the only SC event and $S ; \mathtt{psc}$ is irreflexive for the empty order $S$.

## Depends on

- [RC11-consistent executions](rc11-consistent-executions.md)

## Sources

- O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer, "Repairing sequential consistency in C/C++11", *Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017)*, 2017, <https://plv.mpi-sws.org/scfix/paper.pdf>, Section 3.2 (consistency) and Section 3.4 ("Comparison with C11"), Proposition 2.
