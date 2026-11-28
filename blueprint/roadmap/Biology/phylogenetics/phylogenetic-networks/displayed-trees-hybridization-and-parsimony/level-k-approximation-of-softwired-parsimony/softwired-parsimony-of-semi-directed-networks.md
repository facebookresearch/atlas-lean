# Softwired parsimony of semi-directed networks

A **binary semi-directed network** $N_s$ on $X$ is obtained from a rooted binary phylogenetic network $N_r$ (a **rooted partner** of $N_s$) by deleting the root, suppressing its child, and forgetting the direction of every non-reticulation edge. An unrooted binary $X$-tree $T_u$ is displayed by $N_s$ if some subgraph of $N_s$ using at most one reticulation edge into each reticulation is a subdivision of $T_u$. For an alignment $A = (f_1,\dots,f_n)$ let $PS_{\mathrm{sw}}(A,N_s) = \sum_i \min_{T_u \in D(N_s)} PS(f_i,T_u)$.

1. **Rooting invariance.** For every rooted partner $N_r$ of $N_s$, $PS_{\mathrm{sw}}(A,N_s) = PS_{\mathrm{sw}}(A,N_r)$.
2. **Level bound.** If $N_s$ has level $k$ (some rooted partner is level-$k$), then for every displayed unrooted tree $T_u$,

    $$PS(A,T_u) \le (k+1)\, PS_{\mathrm{sw}}(A,N_s).$$

3. **Failure for unrooted networks.** For fully unrooted networks rooting invariance fails. There is an unrooted level-$1$ network $U$ on five leaves, a binary character $f$ and two orientations $N, N'$ of $U$ with $PS_{\mathrm{sw}}(f,U) = 1$, $PS_{\mathrm{sw}}(f,N) = 2$ and $PS_{\mathrm{sw}}(f,N') = 1$.

## Depends on

- [Displayed-tree parsimony is within a factor $k+1$ of softwired parsimony](displayed-tree-parsimony-within-a-factor-k-plus-one-of-softwired-parsimony.md)

## Expansion

Every unrooted tree displayed by $N_s$ is obtained from a rooted tree displayed by $N_r$ by deleting the root and suppressing its child, and conversely. The construction extends an embedding upward along a root path or removes the root path. Since Fitch scores are unchanged by unrooting, the display sets give the same per-character minima. The level bound then transfers from the rooted case. In an unrooted network, different orientations can create or destroy displayed trees, so no single rooted partner represents $U$.

## Sources

- Janosch Döcker, Simone Linz and Kristina Wicke, "Bounding the Softwired Parsimony Score of a Phylogenetic Network", Bulletin of Mathematical Biology 86 (2024), 121, <https://doi.org/10.1007/s11538-024-01350-9>; numbering as in arXiv:2405.19587: Theorem 2.4, Corollary 2.5, Corollary 8.2 and Theorem 8.3.
