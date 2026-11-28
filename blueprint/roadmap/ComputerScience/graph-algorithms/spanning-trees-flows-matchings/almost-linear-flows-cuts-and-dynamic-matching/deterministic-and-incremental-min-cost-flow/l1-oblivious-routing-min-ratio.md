# An l1 oblivious routing yields an approximate minimum-ratio circulation edge by edge

Let $G$ have lengths $\boldsymbol{\ell} > 0$ and gradients $\mathbf{g}$, with $\mathbf{L} = \mathrm{diag}(\boldsymbol{\ell})$ and edge demand vectors $\mathbf{b}_e = \mathbf{B}^{\top}\mathbf{1}_e$. An $\ell_1$-oblivious routing is a linear map $\mathbf{A} \in \mathbb{R}^{E \times V}$ such that $\mathbf{B}^{\top}\mathbf{A}\mathbf{d} = \mathbf{d}$ for every routable demand $\mathbf{d}$, that is, every $\mathbf{d}$ in the image of $\mathbf{B}^{\top}$, equivalently summing to zero on each connected component of $G$; its quality is $\gamma = \|\mathbf{L}\mathbf{A}\mathbf{B}^{\top}\mathbf{L}^{-1}\|_{1 \to 1}$, the induced $\ell_1$ operator norm on $\mathbb{R}^E$. For every edge $e$ the vector $\mathbf{1}_e - \mathbf{A}\mathbf{b}_e$ is a circulation; let $E' \subseteq E$ be the set of edges for which it is nonzero. If $G$ has a nonzero circulation, then $E' \ne \emptyset$ and

$$
\min_{e \in E',\ \sigma \in \{\pm 1\}}\frac{\mathbf{g}^{\top}\sigma(\mathbf{1}_e - \mathbf{A}\mathbf{b}_e)}{\|\mathbf{L}(\mathbf{1}_e - \mathbf{A}\mathbf{b}_e)\|_1} \le \frac{1}{1 + \gamma}\cdot\min_{\mathbf{B}^{\top}\mathbf{\Delta} = \mathbf{0},\ \mathbf{\Delta} \ne \mathbf{0}}\frac{\mathbf{g}^{\top}\mathbf{\Delta}}{\|\mathbf{L}\mathbf{\Delta}\|_1}.
$$

Edges with $\mathbf{A}\mathbf{b}_e = \mathbf{1}_e$, such as tree edges under a tree routing, are excluded on the left, where their ratio would be $0/0$, and this can happen on a graph with cycles. If $G$ is a forest, then $E' = \emptyset$ and $G$ has no nonzero circulation, so there is no cycle to find. A spanning tree routing (a spanning forest routing if $G$ is disconnected) gives the fundamental tree cycles, and its quality is $\gamma = \max_{e = (u, v)}\boldsymbol{\ell}(T[u, v])/\boldsymbol{\ell}_e$, so $1 + \gamma$ is the maximum stretch in the convention $\mathrm{str}_e = 1 + \boldsymbol{\ell}(T[u, v])/\boldsymbol{\ell}_e$.

## Proof sketch

Suppose $G$ has a nonzero circulation and let $\mathbf{\Delta}^*$ be an optimal one; since $\sum_e\mathbf{\Delta}^*_e\mathbf{b}_e = \mathbf{B}^{\top}\mathbf{\Delta}^* = \mathbf{0}$, linearity gives $\mathbf{\Delta}^* = \sum_{e \in E'}\mathbf{\Delta}^*_e(\mathbf{1}_e - \mathbf{A}\mathbf{b}_e)$, which also shows $E' \ne \emptyset$. By the triangle inequality and $\|\mathbf{L}\mathbf{A}\mathbf{b}_e\|_1 \le \gamma\boldsymbol{\ell}_e$, $\sum_{e \in E'}|\mathbf{\Delta}^*_e|\,\|\mathbf{L}(\mathbf{1}_e - \mathbf{A}\mathbf{b}_e)\|_1 \le (1 + \gamma)\|\mathbf{L}\mathbf{\Delta}^*\|_1$, and the left side is positive. Since $\mathbf{g}^{\top}\mathbf{\Delta}^* \le 0$, taking $\sigma = \mathrm{sign}(\mathbf{\Delta}^*_e)$ and averaging, as for tree cycles, some single term attains the stated ratio.

## Depends on

- [Undirected minimum-ratio cycle problem with gradients and lengths](../almost-linear-flow-interior-point-method/undirected-min-ratio-cycle-problem.md)

## Proof depends on

- [Low stretch preserves a minimum-ratio cycle among fundamental tree cycles](../dynamic-min-ratio-cycle-data-structures/tree-cycles-approximate-min-ratio.md)
- [Every circulation is a combination of fundamental tree cycles](../dynamic-min-ratio-cycle-data-structures/circulation-tree-cycle-decomposition.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Simon Meierhans, Maximilian Probst Gutenberg, "Almost-Linear Time Algorithms for Incremental Graphs: Cycle Detection, SCCs, s-t Shortest Path, and Minimum-Cost Flow", STOC (2024), arXiv:2311.18295.
- Vaclav Rozhon, Christoph Grunau, Bernhard Haeupler, Goran Zuzic, Jason Li, "Undirected (1+epsilon)-Shortest Paths via Minor-Aggregates: Near-Optimal Deterministic Parallel and Distributed Algorithms", STOC (2022), arXiv:2204.05874.
