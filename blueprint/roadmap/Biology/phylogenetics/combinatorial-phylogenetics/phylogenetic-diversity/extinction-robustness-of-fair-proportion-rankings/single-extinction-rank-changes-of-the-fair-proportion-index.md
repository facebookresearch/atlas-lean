# Single-extinction rank changes of the Fair Proportion index

**Setting.** As for Fair Proportion rankings: $T=(T_a,T_b)$ is a rooted binary phylogenetic $X$-tree with maximal pendant subtrees $T_a,T_b$ on $n_a\ge n_b$ leaves, strictly positive edge lengths, Fair Proportion index $FP_T(x)=\sum_{e\in P(T;\rho,x)}\lambda_e/D_e$, and $\widetilde T$ the induced subtree after deleting leaves.

**Theorem.**
1. (Lowest becomes highest) For every $T$ with $n\ge2$ there are strictly positive edge lengths such that $\pi_T$ is strict and, after deleting the leaf $y$ with minimal $FP_T$, the leaf with the second lowest $FP_T$ value has the highest $FP_{\widetilde T}$ value.
2. (Bound for the top species) Let $n\ge3$ and $x^*=\arg\max_xFP_T(x)$. If any leaf $x'\ne x^*$ is deleted, the number $\mathcal N$ of leaves with higher $FP_{\widetilde T}$ value than $x^*$ satisfies $\mathcal N\le n_a-1$ (and $\lfloor\frac{n-1}2\rfloor\le n_a-1$). For every tree there are edge lengths with a strict ranking attaining $\mathcal N=n_a-1$.
3. (Ultrametric caterpillars are robust) If $T$ is an ultrametric caterpillar with $n\ge3$ and $X'\subset X$, then $FP_T(x_i)\ge FP_T(x_j)$ implies $FP_{\widetilde T}(x_i)\ge FP_{\widetilde T}(x_j)$ for all surviving $x_i,x_j$.

## Depends on

- [Fair Proportion rankings reversible by cherry extinctions](fair-proportion-rankings-reversible-by-cherry-extinctions.md)

## Expansion

Deleting some, but not all, leaves of $T_a$ leaves every $FP$ value in $T_b$ unchanged and strictly increases every $FP$ value of the surviving leaves of $T_a$, because only edges of $T_a$ and the root edge into $T_a$ lose descendants. Hence after a single deletion only leaves on the side of the deleted leaf can overtake $x^*$, and since one leaf is gone at most $n_a-1$ of them remain; a construction in the style of the reversibility theorem makes all of them overtake. In an ultrametric caterpillar with cherry $\{x_1,x_2\}$ and spine edges $\lambda_k$, the pendant edge of $x_j$ has length $\sum_{k<j}\lambda_k$ and $FP_T(x_j)=\sum_{k<j}\lambda_k+\sum_{k\ge j}\lambda_k/k$, so $FP_T(x_1)=FP_T(x_2)<FP_T(x_3)<\dots<FP_T(x_n)$; deleting a leaf gives again an ultrametric caterpillar whose FP values are ordered the same way, and induction over deleted leaves gives item 3.

## Sources

- M. Fischer, A. Francis, K. Wicke, "Phylogenetic diversity rankings in the face of extinctions: the robustness of the Fair Proportion index", arXiv:2107.00748 (2021), <https://doi.org/10.48550/arXiv.2107.00748>. Section 3.2 (Theorems 3 and 4), Section 3.3 (Proposition 1) and the Appendix (Lemmas 6 and 8).
