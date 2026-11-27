# Integral minimum-cost flow instances with polynomially bounded data

Let $G = (V, E)$ be a directed multigraph with $n = |V|$ vertices and $m = |E| \ge n$ edges, and let $\mathbf{B} \in \{-1, 0, 1\}^{E \times V}$ be its edge-vertex incidence matrix, whose row for $e = (u, v)$ is $\mathbf{1}_v - \mathbf{1}_u$. An integral minimum-cost flow instance on $G$ consists of demands $\mathbf{d} \in \mathbb{Z}^V$ with $\sum_{v} \mathbf{d}_v = 0$, lower and upper capacities $\mathbf{u}^-, \mathbf{u}^+ \in \mathbb{Z}^E$ with $\mathbf{u}^- \le \mathbf{u}^+$, and costs $\mathbf{c} \in \mathbb{Z}^E$, together with integers $U, C \ge 1$ such that $|\mathbf{u}^{\pm}_e| \le U$, $|\mathbf{d}_v| \le U$ and $|\mathbf{c}_e| \le C$ for all $e \in E$ and $v \in V$.

A flow $\mathbf{f} \in \mathbb{R}^E$ is feasible if $\mathbf{B}^{\top}\mathbf{f} = \mathbf{d}$ and $\mathbf{u}^- \le \mathbf{f} \le \mathbf{u}^+$ coordinatewise; a vector $\mathbf{\Delta} \in \mathbb{R}^E$ with $\mathbf{B}^{\top}\mathbf{\Delta} = \mathbf{0}$ is a circulation. The optimal value is

$$
F^* = \min\{\mathbf{c}^{\top}\mathbf{f} : \mathbf{B}^{\top}\mathbf{f} = \mathbf{d},\ \mathbf{u}^- \le \mathbf{f} \le \mathbf{u}^+\},
$$

and a minimum-cost flow is a feasible flow attaining it. The maximum $s$-$t$ flow problem with integral capacities in $[1, U]$ is the special case obtained by adding an arc $(t, s)$ of capacity $mU$ and cost $-1$, giving all other arcs cost $0$ and lower capacity $0$, and taking $\mathbf{d} = \mathbf{0}$.

## Depends on

- [Feasible flow](../../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/is-feasible-flow.md)
- [Oriented incidence matrix of a multigraph](../../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
