# Stretch of an edge with respect to a rooted spanning forest

Let $F$ be a rooted spanning forest of $G = (V, E)$ with lengths $\boldsymbol{\ell} > 0$, and let $\mathrm{root}^F_x$ be the root of the component of $F$ containing $x$. For $e = (u, v) \in E$ the stretch of $e$ with respect to $F$ is

$$
\mathrm{str}^{F, \boldsymbol{\ell}}_e = \begin{cases} 1 + \langle\boldsymbol{\ell}, |\mathbf{p}(F[u, v])|\rangle/\boldsymbol{\ell}_e & \text{if } \mathrm{root}^F_u = \mathrm{root}^F_v, \\ 1 + \langle\boldsymbol{\ell}, |\mathbf{p}(F[u, \mathrm{root}^F_u])| + |\mathbf{p}(F[v, \mathrm{root}^F_v])|\rangle/\boldsymbol{\ell}_e & \text{otherwise.} \end{cases}
$$

When $F$ is a spanning tree this is the stretch of *Edge stretch with respect to a spanning tree and edge lengths*. A low-stretch forest of $G$ is a triple $(T, F, \widetilde{\mathrm{str}})$ of a spanning tree $T$, a rooted forest $F \subseteq T$ and stretch overestimates $\widetilde{\mathrm{str}}_e \ge \mathrm{str}^{F, \boldsymbol{\ell}}_e$.

## Depends on

- [Edge stretch with respect to a spanning tree and edge lengths](edge-stretch-wrt-spanning-tree.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
