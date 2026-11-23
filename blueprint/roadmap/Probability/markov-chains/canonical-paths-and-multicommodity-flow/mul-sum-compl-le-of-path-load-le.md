# The cut bound $\pi(A)\pi(A^c) \le \rho\, Q(A, A^c)$

If $\pi \ge 0$, every $\gamma_{xy}$ ($x \ne y$) runs from $x$ to $y$, and every edge load is at most $\rho\,\pi(u)P(u,v)$, then for every set $A$ of states

$$\pi(A)\,\pi(A^c) \;\le\; \rho \sum_{u \in A,\ v \notin A} \pi(u)P(u,v).$$

All $\pi(A)\pi(A^c)$ units sent from $A$ to its complement must cross the cut, whose capacity is $Q(A,A^c)$. This is inequality (13), $\Phi' \ge 1/\rho$ for the symmetrised conductance $\Phi' = \min_A Q(A,A^c)/(\pi(A)\pi(A^c))$, of A. Sinclair, *Combinatorics, Probability and Computing* 1 (1992); Sinclair describes it as the trivial direction of a max-flow min-cut theorem for this multicommodity flow problem.
