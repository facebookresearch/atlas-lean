# Edge stretch with respect to a spanning tree and edge lengths

Let $G = (V, E)$ be a connected graph with lengths $\boldsymbol{\ell} \in \mathbb{R}^E_{>0}$ and let $T$ be a spanning tree of $G$. For $e = (u, v) \in E$ let $T[u, v]$ be the unique $u$-$v$ path in $T$. The stretch of $e$ is

$$
\mathrm{str}^{T, \boldsymbol{\ell}}_e = 1 + \frac{\sum_{e' \in T[u, v]} \boldsymbol{\ell}_{e'}}{\boldsymbol{\ell}_e},
$$

so that $\mathrm{str}_e \ge 1$, with $\mathrm{str}_e = 2$ for tree edges. For weights $\mathbf{v} \in \mathbb{R}^E_{>0}$ and $\gamma \ge 1$, the tree $T$ is a $\gamma$-low-stretch spanning tree with respect to $\mathbf{v}$ if $\sum_{e \in E} \mathbf{v}_e\, \mathrm{str}^{T, \boldsymbol{\ell}}_e \le \gamma \|\mathbf{v}\|_1$; the case $\mathbf{v} = \mathbf{1}$ bounds the average stretch by $\gamma$.

## Depends on

- [Spanning tree](../../../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/is-spanning-tree.md)

## Sources

- Noga Alon, Richard M. Karp, David Peleg, Douglas West, "A Graph-Theoretic Game and Its Application to the k-Server Problem", SIAM J. Comput. 24(1) (1995).
- Michael Elkin, Yuval Emek, Daniel A. Spielman, Shang-Hua Teng, "Lower-Stretch Spanning Trees", STOC (2005), arXiv:cs/0411064.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
