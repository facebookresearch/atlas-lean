# Low stretch preserves a minimum-ratio cycle among fundamental tree cycles

Let $G$ have gradients $\mathbf{g}$ and lengths $\boldsymbol{\ell}$, let $T$ be a spanning tree, and let $\mathbf{\Delta}$ be the circulation that routes one unit of flow around a cycle $C$ of $G$ (so $\mathbf{\Delta}_e = \pm 1$ for $e \in C$, the sign recording the edge's orientation, and $\mathbf{\Delta}_e = 0$ otherwise), with $\mathbf{g}^{\top}\mathbf{\Delta} < 0$ and

$$
\sum_{e \in E} \boldsymbol{\ell}_e\, \mathrm{str}^{T, \boldsymbol{\ell}}_e\, |\mathbf{\Delta}_e| \le \gamma\, \|\mathbf{L}\mathbf{\Delta}\|_1 .
$$

Then there are an off-tree edge $e$ of $C$ and a sign $\sigma \in \{\pm 1\}$ with

$$
\frac{\mathbf{g}^{\top}(\sigma\boldsymbol{\chi}^T_e)}{\|\mathbf{L}\boldsymbol{\chi}^T_e\|_1} \le \frac{1}{\gamma}\cdot\frac{\mathbf{g}^{\top}\mathbf{\Delta}}{\|\mathbf{L}\mathbf{\Delta}\|_1}.
$$

In particular, taking for $\mathbf{\Delta}$ a minimum-ratio cycle routing one unit of flow, if $T$ stretches it by at most $\gamma$ in this sense, some single tree cycle is a $(1/\gamma)$-approximate minimum-ratio cycle, and it can be found by scanning the $m - n + 1$ off-tree edges.

## Proof sketch

By *Every circulation is a combination of fundamental tree cycles*, $\mathbf{\Delta} = \sum_{e \in C \setminus T}\mathbf{\Delta}_e\,\boldsymbol{\chi}^T_e$ (the tree paths of consecutive off-tree edges cancel), so $\mathbf{g}^{\top}\mathbf{\Delta} = \sum_{e \notin T}\mathbf{\Delta}_e\,\mathbf{g}^{\top}\boldsymbol{\chi}^T_e$, while $\sum_{e \notin T}|\mathbf{\Delta}_e|\,\|\mathbf{L}\boldsymbol{\chi}^T_e\|_1 = \sum_{e \notin T}\boldsymbol{\ell}_e\mathrm{str}_e|\mathbf{\Delta}_e| \le \gamma\|\mathbf{L}\mathbf{\Delta}\|_1$. A ratio of sums is at least the minimum of the termwise ratios, so with $\sigma = \mathrm{sign}(\mathbf{\Delta}_e)$ some term satisfies $\mathbf{g}^{\top}(\sigma\boldsymbol{\chi}_e)/\|\mathbf{L}\boldsymbol{\chi}_e\|_1 \le \mathbf{g}^{\top}\mathbf{\Delta}/(\gamma\|\mathbf{L}\mathbf{\Delta}\|_1)$.

## Depends on

- [Edge stretch with respect to a spanning tree and edge lengths](edge-stretch-wrt-spanning-tree.md)
- [Fundamental tree cycles as circulations](fundamental-tree-cycle-circulation.md)
- [Undirected minimum-ratio cycle problem with gradients and lengths](../almost-linear-flow-interior-point-method/undirected-min-ratio-cycle-problem.md)

## Proof depends on

- [Every circulation is a combination of fundamental tree cycles](circulation-tree-cycle-decomposition.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671, Section 2.2 (the witness $\mathbf{\Delta}^*$, "a cycle that routes one unit of flow along the cycle").
- Li Chen, Rasmus Kyng, Yang P. Liu, Simon Meierhans, Maximilian Probst Gutenberg, "Almost-Linear Time Algorithms for Incremental Graphs: Cycle Detection, SCCs, s-t Shortest Path, and Minimum-Cost Flow", STOC (2024), arXiv:2311.18295.
