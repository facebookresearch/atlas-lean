# Hidden witnesses pass to core graphs and sparsified core graphs with bounded loss

Let $(\mathbf{c}, \mathbf{w})$ be a valid pair on $G$ with lengths $\boldsymbol{\ell}$ and let $(T, F, \widetilde{\mathrm{str}})$ be a low-stretch forest. Define $\mathbf{c}^{\mathcal{C}}_{\hat{e}} = \mathbf{c}_e$ and $\mathbf{w}^{\mathcal{C}}_{\hat{e}} = \widetilde{\mathrm{str}}_e\mathbf{w}_e$ on $\mathcal{C}(G, F)$, and for a sparsified core graph with embedding $\Pi$ define $\mathbf{c}^{\mathcal{S}} = \sum_{\hat{e}}\mathbf{c}^{\mathcal{C}}_{\hat{e}}\Pi(\hat{e})$ and $\mathbf{w}^{\mathcal{S}} = 2\sum_{\hat{e}}\mathbf{w}^{\mathcal{C}}_{\hat{e}}|\Pi(\hat{e})|$, where $\Pi(\hat{e})$ denotes the signed path vector. Then $(\mathbf{c}^{\mathcal{C}}, \mathbf{w}^{\mathcal{C}})$ is a valid pair on $\mathcal{C}(G, F)$, $(\mathbf{c}^{\mathcal{S}}, \mathbf{w}^{\mathcal{S}})$ is a valid pair on $\mathcal{S}(G, F)$, and

$$
\|\mathbf{w}^{\mathcal{C}}\|_1 \le \sum_{e}\widetilde{\mathrm{str}}_e\mathbf{w}_e, \qquad \|\mathbf{w}^{\mathcal{S}}\|_1 \le 2\gamma_\ell\|\mathbf{w}^{\mathcal{C}}\|_1 .
$$

Moreover $\langle\mathbf{g}^{\mathcal{C}}, \mathbf{c}^{\mathcal{C}}\rangle = \langle\mathbf{g}, \mathbf{c}\rangle$, so the witness keeps its gradient value while its width grows by the stretch.

## Proof sketch

Contracting the components of $F$ maps a circulation to a circulation, and $|\boldsymbol{\ell}^{\mathcal{C}}_{\hat{e}}\mathbf{c}_e| = \widetilde{\mathrm{str}}_e|\boldsymbol{\ell}_e\mathbf{c}_e| \le \mathbf{w}^{\mathcal{C}}_{\hat{e}}$. The gradient identity holds because the tree terms $\langle\mathbf{g}, \mathbf{p}(T[v,u])\rangle$ weighted by a circulation sum to the gradient of a circulation supported on $T$, which is zero by *Every circulation is a combination of fundamental tree cycles*. Rerouting each core edge along its embedding path keeps a circulation, the factor-$2$ length comparability gives validity, and each path has at most $\gamma_\ell$ edges, which yields the norm bound.

## Depends on

- [Sparsified core graphs with short low-congestion embeddings](sparsified-core-graph-embedding.md)
- [Hidden stable flow chasing property of a dynamic min-ratio cycle instance](hidden-stable-flow-chasing.md)
- [Core graph of a low-stretch forest with stretched lengths and tree-shifted gradients](core-graph-of-low-stretch-forest.md)

## Proof depends on

- [Every circulation is a combination of fundamental tree cycles](circulation-tree-cycle-decomposition.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
