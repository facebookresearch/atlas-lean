# Duality for distributional robustness over a finite transport ball

Let $\xi_1, \dots, \xi_m$ be support points with nominal probabilities $p_i \ge 0$, $\sum_i p_i = 1$, transport costs $d_{ij} \ge 0$ with $d_{ii} = 0$, losses $\ell_j$ at the points and a radius $\varepsilon \ge 0$. The worst-case expected loss over distributions on the same points within transport cost $\varepsilon$,

$$
\max\Bigl\{\sum_{i,j}\pi_{ij}\ell_j : \pi \ge 0,\ \sum_j \pi_{ij} = p_i,\ \sum_{i,j} d_{ij}\pi_{ij} \le \varepsilon\Bigr\},
$$

equals $\min\{\gamma\varepsilon + \sum_i p_i s_i : \gamma \ge 0,\ s_i \ge \ell_j - \gamma d_{ij} \text{ for all } i, j\}$. The primal is feasible ($\pi_{ii} = p_i$) and bounded, so this is linear programming duality. Wasserstein balls of distributions with continuous support are not covered.

## Proof depends on

- [Strong linear programming duality](../linear-programming/strong-linear-programming-duality.md): strong duality for the feasible bounded primal.

## Sources

- A. Schrijver, *A Course in Combinatorial Optimization*, lecture notes, CWI and University of Amsterdam, 2017, <https://homepages.cwi.nl/~lex/files/dict.pdf>, §2.4, Theorem 2.6 and Corollary 2.6a (finite linear programming duality)
