# Incremental thresholded minimum-cost flow problem

The incremental thresholded minimum-cost flow problem is given a directed graph $G = (V, E)$ with capacities $\mathbf{u} \in [1, U]^E$ and costs $\mathbf{c} \in [-C, C]^E$, undergoing edge insertions, together with a fixed demand vector $\mathbf{d} \in \mathbb{R}^V$ with $\sum_v\mathbf{d}_v = 0$ and a threshold $F$. After every insertion the algorithm must report whether there is a flow $\mathbf{f}$ with $\mathbf{B}^{\top}\mathbf{f} = \mathbf{d}$, $\mathbf{0} \le \mathbf{f} \le \mathbf{u}$ and $\mathbf{c}^{\top}\mathbf{f} \le F$. Since a newly inserted edge may carry zero flow, the optimal cost is nonincreasing under insertions, so the answer is monotone: it is no up to some time and yes from then on, where that time may be zero, before any insertion, or may never come if no insertion makes $\mathbf{d}$ routable within cost $F$; the problem is equivalent to detecting that time.

## Depends on

- [Integral minimum-cost flow instances with polynomially bounded data](../almost-linear-flow-interior-point-method/integral-min-cost-flow-instance.md)
- [Dynamic graph problems](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Simon Meierhans, Maximilian Probst Gutenberg, "Almost-Linear Time Algorithms for Incremental Graphs: Cycle Detection, SCCs, s-t Shortest Path, and Minimum-Cost Flow", STOC (2024), arXiv:2311.18295.
- Jan van den Brand, Yang P. Liu, Aaron Sidford, "Dynamic Maxflow via Dynamic Interior Point Methods", STOC (2023), arXiv:2212.06315.
