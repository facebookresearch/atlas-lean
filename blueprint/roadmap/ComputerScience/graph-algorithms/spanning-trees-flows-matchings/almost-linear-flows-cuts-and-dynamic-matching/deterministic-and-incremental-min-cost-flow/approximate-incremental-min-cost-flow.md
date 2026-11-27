# Approximate incremental minimum-cost flow, maximum flow and bipartite matching

There is a deterministic algorithm that, given an incremental directed graph with capacities in $[1, U]$ and costs in $[1, C]$ with $U, C \le m^{O(1)}$, and an integral demand $\mathbf{d}$, maintains throughout the insertions, in total time $m\epsilon^{-1}\exp(O(\log^{167/168} m\log\log m))$ for $\epsilon \in (0, 1]$, the following answer: that $\mathbf{d}$ is infeasible, while no flow routes it; the zero flow, when $\mathbf{d} = \mathbf{0}$; and otherwise a flow of cost at most $(1 + \epsilon)\mathrm{OPT}$, where $\mathrm{OPT} \ge 1$ is the current minimum cost. As special cases it maintains $(1 - \epsilon)$-approximate maximum flows and approximate maximum-weight bipartite matchings in incremental graphs. Under the online matrix-vector multiplication conjecture the linear dependence on $\epsilon^{-1}$ is optimal, since exact incremental bipartite matching already requires $m n^{1 - o(1)}$ total time.

## Proof sketch

If $\mathbf{d} = \mathbf{0}$ the zero flow is optimal. Otherwise some vertex has $|\mathbf{d}_v| \ge 1$ by integrality, so every feasible flow carries at least one unit on edges of cost at least $1$ and $\mathrm{OPT} \ge 1$, while $\mathrm{OPT} \le \sum_e \mathbf{c}_e\mathbf{u}_e \le mCU$ once a feasible flow exists. Run one instance of *Incremental thresholded minimum-cost flow in almost-linear total time* for each threshold $(1 + \epsilon)^i$, $i = 0, 1, \ldots, \lceil\log_{1+\epsilon}(mCU)\rceil = O(\epsilon^{-1}\log(mCU))$; the demand is infeasible exactly while no instance has reported a flow. Because $\mathrm{OPT}$ is nonincreasing under insertions, the smallest threshold $(1 + \epsilon)^i$ reached so far satisfies $(1 + \epsilon)^{i-1} < \mathrm{OPT}$ when $i \ge 1$, and $\mathrm{OPT} \ge 1 = (1 + \epsilon)^0$ when $i = 0$, so its flow is within a factor $1 + \epsilon$ of optimal. The lower bound statement follows from the known OMv-hardness of exact incremental bipartite matching by choosing $\epsilon < 1/n$.

## Depends on

- [The online matrix-vector multiplication conjecture](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-online-matrix-vector-multiplication.md)
- [Matching in a bipartite graph](../../maximum-bipartite-matching/is-matching.md)

## Proof depends on

- [Incremental thresholded minimum-cost flow in almost-linear total time](incremental-thresholded-mcf-almost-linear.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Simon Meierhans, Maximilian Probst Gutenberg, "Almost-Linear Time Algorithms for Incremental Graphs: Cycle Detection, SCCs, s-t Shortest Path, and Minimum-Cost Flow", STOC (2024), arXiv:2311.18295.
