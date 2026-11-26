# An l1 oblivious routing yields an approximate minimum-ratio circulation edge by edge

Let $G$ have lengths $\boldsymbol{\ell} > 0$ and gradients $\mathbf{g}$, with $\mathbf{L} = \mathrm{diag}(\boldsymbol{\ell})$ and edge demand vectors $\mathbf{b}_e = \mathbf{B}^{\top}\mathbf{1}_e$. An $\ell_1$-oblivious routing is a linear map $\mathbf{A} \in \mathbb{R}^{E \times V}$ such that $\mathbf{B}^{\top}\mathbf{A}\mathbf{d} = \mathbf{d}$ for every $\mathbf{d} \perp \mathbf{1}$; its quality is $\|\mathbf{L}\mathbf{A}\mathbf{L}^{-1}\|_{1 \to 1}$ in the sense of the induced operator norm on edge vectors through $\mathbf{d} = \mathbf{B}^{\top}\mathbf{x}$. For every edge $e$ the vector $\mathbf{1}_e - \mathbf{A}\mathbf{b}_e$ is a circulation, and

$$
\min_{e \in E,\ \sigma \in \{\pm 1\}}\frac{\mathbf{g}^{\top}\sigma(\mathbf{1}_e - \mathbf{A}\mathbf{b}_e)}{\|\mathbf{L}(\mathbf{1}_e - \mathbf{A}\mathbf{b}_e)\|_1} \le \frac{1}{1 + \|\mathbf{L}\mathbf{A}\mathbf{L}^{-1}\|_{1 \to 1}}\cdot\min_{\mathbf{B}^{\top}\mathbf{\Delta} = \mathbf{0}}\frac{\mathbf{g}^{\top}\mathbf{\Delta}}{\|\mathbf{L}\mathbf{\Delta}\|_1}.
$$

A spanning tree routing gives the fundamental tree cycles, and low-stretch trees give quality equal to their stretch.

## Proof sketch

Let $\mathbf{\Delta}^*$ be an optimal circulation; since $\sum_e\mathbf{\Delta}^*_e\mathbf{b}_e = \mathbf{B}^{\top}\mathbf{\Delta}^* = \mathbf{0}$, linearity gives $\mathbf{\Delta}^* = \sum_e\mathbf{\Delta}^*_e(\mathbf{1}_e - \mathbf{A}\mathbf{b}_e)$. By the triangle inequality and the quality bound, $\sum_e|\mathbf{\Delta}^*_e|\,\|\mathbf{L}(\mathbf{1}_e - \mathbf{A}\mathbf{b}_e)\|_1 \le (1 + \|\mathbf{L}\mathbf{A}\mathbf{L}^{-1}\|_{1\to 1})\|\mathbf{L}\mathbf{\Delta}^*\|_1$. Averaging, as for tree cycles, some single term attains the stated ratio.

## Depends on

- [Undirected minimum-ratio cycle problem with gradients and lengths](../almost-linear-flow-interior-point-method/undirected-min-ratio-cycle-problem.md)

## Proof depends on

- [Low stretch preserves a minimum-ratio cycle among fundamental tree cycles](../dynamic-min-ratio-cycle-data-structures/tree-cycles-approximate-min-ratio.md)
- [Every circulation is a combination of fundamental tree cycles](../dynamic-min-ratio-cycle-data-structures/circulation-tree-cycle-decomposition.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Simon Meierhans, Maximilian Probst Gutenberg, "Almost-Linear Time Algorithms for Incremental Graphs: Cycle Detection, SCCs, s-t Shortest Path, and Minimum-Cost Flow", STOC (2024), arXiv:2311.18295.
- Vaclav Rozhon, Christoph Grunau, Bernhard Haeupler, Goran Zuzic, Jason Li, "Undirected (1+epsilon)-Shortest Paths via Minor-Aggregates: Near-Optimal Deterministic Parallel and Distributed Algorithms", STOC (2022), arXiv:2204.05874.
