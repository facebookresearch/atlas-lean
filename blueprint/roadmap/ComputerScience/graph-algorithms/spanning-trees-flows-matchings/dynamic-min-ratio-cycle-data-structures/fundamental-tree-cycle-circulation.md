# Fundamental tree cycles as circulations

Let $T$ be a spanning tree of a directed graph $G = (V, E)$, oriented edgewise as in $G$. For vertices $x, y$ let $\mathbf{p}(T[x, y]) \in \{-1, 0, 1\}^E$ be the signed indicator vector of the $x$-$y$ path in $T$, routing one unit from $x$ to $y$, so that $\mathbf{p}(T[x, y]) + \mathbf{p}(T[y, z]) = \mathbf{p}(T[x, z])$. For an edge $e = (u, v) \in E \setminus T$ the fundamental tree cycle is the circulation

$$
\boldsymbol{\chi}^T_e = \mathbf{1}_e + \mathbf{p}(T[v, u]).
$$

For lengths $\boldsymbol{\ell}$ one has $\|\mathbf{L}\boldsymbol{\chi}^T_e\|_1 = \boldsymbol{\ell}_e\, \mathrm{str}^{T, \boldsymbol{\ell}}_e$.

## Depends on

- [Edge stretch with respect to a spanning tree and edge lengths](edge-stretch-wrt-spanning-tree.md)
- [Undirected minimum-ratio cycle problem with gradients and lengths](../almost-linear-flow-interior-point-method/undirected-min-ratio-cycle-problem.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
