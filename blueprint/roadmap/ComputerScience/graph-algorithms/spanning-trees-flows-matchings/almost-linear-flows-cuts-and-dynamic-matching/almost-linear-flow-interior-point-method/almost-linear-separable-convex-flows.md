# Almost-linear time high-accuracy flows for separable convex costs

Let $G$ be a graph with $m$ edges and demand $\mathbf{d}$ with entries bounded by $\exp(\log^{O(1)} m)$. For each edge let $h_e : \mathbb{R} \to \mathbb{R} \cup \{+\infty\}$ be convex and suppose its epigraph admits an $O(1)$-self-concordant barrier whose value, gradient and Hessian are computable in $\widetilde{O}(1)$ time and whose relevant quantities are bounded by $\exp(\log^{O(1)} m)$ on the region of interest. Write $h(\mathbf{f}) = \sum_{e} h_e(\mathbf{f}_e)$. Then for every constant $C > 0$ there is an algorithm running in $m^{1+o(1)}$ time that outputs a flow $\mathbf{f}$ with $\mathbf{B}^{\top}\mathbf{f} = \mathbf{d}$ and

$$
h(\mathbf{f}) \le \min_{\mathbf{B}^{\top}\mathbf{f}^* = \mathbf{d}} h(\mathbf{f}^*) + \exp(-\log^{C} m).
$$

This covers $p$-norm flows with weighted terms $w|x|^p$ for $p \le \widetilde{O}(1)$, entropy-regularized optimal transport and its dual, matrix scaling to prescribed row and column sums.

## Proof sketch

Each edge is lifted to the epigraph variable $(x, y)$ with the barrier for $\{y \ge h_e(x)\}$, and the potential function replaces the power barriers by these self-concordant barriers with a path parameter $t$ that is doubled in $\widetilde{O}(1)$ phases. Within a phase the same analysis as for linear costs shows that $m^{-o(1)}$-approximate minimum-ratio cycles in the induced lengths and gradients decrease the potential by $m^{-o(1)}$ per step, and the updates satisfy the same hidden stability property, so the dynamic minimum-ratio cycle data structure runs in $m^{1+o(1)}$ total time. For $|x|^p$ the barrier $-2\log y - \log(y^{2/p} - x^2)$ is $4$-self-concordant, giving the listed applications.

## Depends on

- [Self-concordant barrier](../../../../../Analysis/convex-analysis-and-variations/self-concordant-functions-and-barriers/is-self-concordant-barrier.md)
- [Oriented incidence matrix of a multigraph](../../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)

## Proof depends on

- [Potential-reduction l1 IPM: min-cost flow from m^(1+o(1)) approximate min-ratio cycles](l1-potential-reduction-ipm.md)
- [The l1 IPM reduces min-cost flow to an approximate dynamic min-ratio cycle problem](ipm-reduces-to-dynamic-min-ratio-cycle.md)
- [Randomized dynamic min-ratio cycle data structure under hidden stable flow chasing](../dynamic-min-ratio-cycle-data-structures/randomized-dynamic-min-ratio-cycle.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
