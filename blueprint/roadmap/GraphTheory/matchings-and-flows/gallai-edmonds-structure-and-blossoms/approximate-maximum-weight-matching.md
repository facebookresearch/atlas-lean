# Approximate maximum weight matchings in general graphs

Let $G = (V, E)$ be a finite simple graph with $n$ vertices, $m$ edges and weights $w : E \to \mathbb{R}_{\ge 0}$, and write $w(M) = \sum_{e \in M} w(e)$. For $\varepsilon \in (0, 1)$, a *$(1 - \varepsilon)$-approximate maximum weight matching* is a matching $M$ with

$$
w(M) \ge (1 - \varepsilon) \max\{ w(M') : M' \text{ a matching of } G \} .
$$

In the unweighted case a matching $M$ is a *$(1 + \varepsilon)$-approximate maximum matching* if $(1 + \varepsilon)|M| \ge \nu(G)$. If all weights are integers in $\{0, 1, \dots, N\}$ then the optimum is at most $nN/2$, so any $(1 - \varepsilon)$-approximation with $\varepsilon < 2/(nN)$ is optimal.

## Sources

- R. Duan, S. Pettie, "Linear-Time Approximation for Maximum Weight Matching", Journal of the ACM 61 (2014).
- R. Duan, S. Pettie, H.-H. Su, "Scaling Algorithms for Weighted Matching in General Graphs", ACM Transactions on Algorithms 14 (2018), SODA (2017), arXiv:1411.1919.
