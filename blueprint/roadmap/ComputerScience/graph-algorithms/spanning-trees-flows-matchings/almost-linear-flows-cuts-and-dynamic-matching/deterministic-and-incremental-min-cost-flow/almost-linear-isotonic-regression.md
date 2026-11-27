# High-accuracy l_p isotonic regression on DAGs in almost-linear time

Fix $p \in [1, \infty]$ and a constant $C > 0$. There is an algorithm that, given a directed acyclic graph $G = (V, E)$ with $m$ edges and observations $\mathbf{y} \in \mathbb{R}^V$ with entries bounded by $\exp(\log^{O(1)} m)$ in absolute value, computes in $m^{1+o(1)}$ time, with high probability, a vector $\mathbf{x}$ with $\mathbf{x}_u \le \mathbf{x}_v$ for every arc $(u, v) \in E$ and

$$
\|\mathbf{x} - \mathbf{y}\|_p \le \min_{\mathbf{x}' :\ \mathbf{x}'_u \le \mathbf{x}'_v\ \forall (u,v) \in E}\|\mathbf{x}' - \mathbf{y}\|_p + \exp(-\log^{C} m).
$$

The bound depends on the number of arcs of $G$, not of its transitive closure.

## Proof sketch

By minimax duality, $\min_{\mathbf{B}\mathbf{x} \ge 0}\|\mathbf{x} - \mathbf{y}\|_p$ equals $\max\{-\mathbf{f}^{\top}\mathbf{B}\mathbf{y} : \mathbf{f} \ge 0,\ \|\mathbf{B}^{\top}\mathbf{f}\|_q \le 1\}$ with $1/p + 1/q = 1$, which after rescaling is a flow problem with separable convex costs: linear costs and nonnegativity on arcs and a $q$-norm cost on edges from the vertices to one new vertex. Each term has a $4$-self-concordant barrier, so *Almost-linear time high-accuracy flows for separable convex costs* solves it to accuracy $\exp(-\log^{C'} m)$, and a primal solution is recovered from the near-optimal dual flow through the optimality conditions.

## Depends on

- [Acyclic directed graph](../../../traversal-and-connectivity/topological-sorting/is-acyclic.md)

## Proof depends on

- [Almost-linear time high-accuracy flows for separable convex costs](../almost-linear-flow-interior-point-method/almost-linear-separable-convex-flows.md)
- [Self-concordant barrier](../../../../../Analysis/convex-analysis-and-variations/self-concordant-functions-and-barriers/is-self-concordant-barrier.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Rasmus Kyng, Anup Rao, Sushant Sachdeva, "Fast, Provable Algorithms for Isotonic Regression in all l_p-norms", NeurIPS (2015).
