# Core graph of a low-stretch forest with stretched lengths and tree-shifted gradients

Let $(T, F, \widetilde{\mathrm{str}})$ be a low-stretch forest of $G$ with lengths $\boldsymbol{\ell}$ and gradients $\mathbf{g}$, where $T$ is a fixed tree that need not remain a subgraph of a dynamic $G$. The core graph $\mathcal{C}(G, F)$ has the vertex and edge set of the contraction $G/F$ of every component of $F$ to its root. For $e = (u, v) \in E(G)$ with image $\hat{e}$ its length and gradient are

$$
\boldsymbol{\ell}^{\mathcal{C}(G,F)}_{\hat{e}} = \widetilde{\mathrm{str}}_e\,\boldsymbol{\ell}_e, \qquad \mathbf{g}^{\mathcal{C}(G,F)}_{\hat{e}} = \mathbf{g}_e + \langle\mathbf{g}, \mathbf{p}(T[v, u])\rangle,
$$

with the convention that the tree term is $0$ when $u, v$ are disconnected in $T$. When $F$ comes from *Dynamic low-stretch forests with stable stretch overestimates*, $\mathcal{C}(G, F)$ has $O(m/k)$ vertices initially, so it reduces the vertex count while keeping all edges; lengths and gradients of core edges do not change when edges of $F$ are deleted.

## Depends on

- [Stretch of an edge with respect to a rooted spanning forest](rooted-forest-edge-stretch.md)
- [Fundamental tree cycles as circulations](fundamental-tree-cycle-circulation.md)
- [Dynamic low-stretch forests with stable stretch overestimates](dynamic-low-stretch-forest.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
