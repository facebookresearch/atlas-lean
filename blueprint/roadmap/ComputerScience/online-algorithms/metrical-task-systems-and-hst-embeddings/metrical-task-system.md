# Metrical task systems

A *metrical task system* (MTS) on a finite metric space $(M, d)$ with $|M| = n$ starts in a state $x_0 \in M$. At each time $t = 1, 2, \dots$ a cost function $\ell_t : M \to [0, \infty]$ arrives, and an online algorithm chooses a state $x_t$, paying $d(x_{t-1}, x_t) + \ell_t(x_t)$, without knowledge of future cost functions. The offline optimum chooses all states knowing the whole sequence. Paging and $k$-server are special cases with suitably chosen state spaces and cost functions; convex body chasing is the analogous problem on the infinite state space $\mathbb{R}^d$.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Sources

- Allan Borodin, Nathan Linial, Michael E. Saks, "An Optimal On-Line Algorithm for Metrical Task System", Journal of the ACM 39(4) (1992).
