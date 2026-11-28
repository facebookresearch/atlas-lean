# Almost-linear time high-accuracy flows for separable convex costs

Let $G$ be a graph with $m$ edges and $\mathbf{d}$ a demand. For each edge let $h_e : \mathbb{R} \to \mathbb{R} \cup \{+\infty\}$ be convex and let $\psi_e$ be a $\nu$-self-concordant barrier for the epigraph $\{(x, y) : y \ge h_e(x)\}$. Suppose that, for a parameter $K = \widetilde{O}(1)$:

1. gradients and Hessians of every $\psi_e$ are computable in $\widetilde{O}(1)$ time;
2. $\|\mathbf{d}\|_\infty \le m^K$, the flows considered satisfy $|\mathbf{f}_e| \le m^K$, and $|h_e(x)| \le O(m^K + |x|^K)$ for all $x$;
3. there are a flow $\mathbf{f}^{(0)}$ with $\mathbf{B}^{\top}\mathbf{f}^{(0)} = \mathbf{d}$ and values $|y^{(0)}_e| \le m^K$ with $m^{-K}\mathbf{I} \preceq \nabla^2\psi_e(\mathbf{f}^{(0)}_e, y^{(0)}_e) \preceq m^K\mathbf{I}$ and $\psi_e(\mathbf{f}^{(0)}_e, y^{(0)}_e) \le K$, after shifting each $\psi_e$ so that its infimum over $|x|, |y| \le m^K$ is $0$;
4. $\nu \le \widetilde{O}(1)$, so that the step parameters of the method can be taken below $1/(1000\nu)$;
5. $\nabla^2\psi_e(x, y) \preceq \exp(\log^{O(1)} m)\,\mathbf{I}$ whenever $|x|, |y| \le m^K$ and $\psi_e(x, y) \le \widetilde{O}(1)$.

Write $h(\mathbf{f}) = \sum_{e} h_e(\mathbf{f}_e)$. Then for every constant $C > 0$ there is an algorithm running in $m^{1+o(1)}$ time that outputs a flow $\mathbf{f}$ with $\mathbf{B}^{\top}\mathbf{f} = \mathbf{d}$ and

$$
h(\mathbf{f}) \le \min_{\mathbf{B}^{\top}\mathbf{f}^* = \mathbf{d}} h(\mathbf{f}^*) + \exp(-\log^{C} m).
$$

The algorithm succeeds with high probability. This covers flows whose edge costs are sums of $\widetilde{O}(1)$ terms $w|x|^p$ with $p \le \widetilde{O}(1)$ and $w \in [0, \exp(\log^{O(1)} m)]$, entropy-regularized optimal transport, and, through its dual, matrix scaling: given a nonnegative $n \times n$ matrix $A$ whose nonzero entries lie in $[n^{-O(1)}, n^{O(1)}]$ and whose support contains a perfect matching, positive diagonal matrices $X, Y$ such that all row and column sums of $XAY$ are within $\exp(-\log^{C} n)$ of $1$ are found in $\mathrm{nnz}(A)^{1+o(1)}$ time. The support condition is necessary: for $\mathrm{diag}(1, 0)$ the second row sum of $XAY$ is always $0$, and in general the dual flow problem, which sends one unit out of every row and into every column along the support, then has no feasible flow, so such an instance is reported infeasible.

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
