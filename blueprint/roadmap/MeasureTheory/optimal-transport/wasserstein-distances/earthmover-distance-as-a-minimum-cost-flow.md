# Earthmover distance as a minimum-cost flow

Let $V$ be a finite set with a metric $d$, and let $S$ and $T$ be probability distributions on $V$. The $d$-earthmover distance
between $S$ and $T$ is the minimum of $\sum_{x, y \in V} h(x, y) \, d(x, y)$ over the couplings $h$ of $S$ and $T$, the functions
$h : V \times V \to [0, \infty)$ with $\sum_{y \in V} h(x, y) = S(x)$ and $\sum_{y \in V} h(y, x) = T(x)$ for every $x \in V$. It
equals the minimum of $\sum_{x, y \in V} f(x, y) \, d(x, y)$ over all $f : V \times V \to [0, \infty)$ with

$$\sum_{y \in V} f(x, y) = \sum_{y \in V} f(y, x) + S(x) - T(x) \quad \text{for every } x \in V,$$

that is, over the nonnegative flows on the complete directed graph on $V$ whose net outflow at each vertex $x$ is $S(x) - T(x)$,
a unit of flow on the arc from $x$ to $y$ costing $d(x, y)$.

## Proof

Every coupling of $S$ and $T$ is such a flow with the same cost, so the minimum over flows is at most the earthmover distance.
Conversely, a flow is a sum of nonnegative flows along paths, each from a vertex with $S(x) > T(x)$ to one with $S(x) < T(x)$,
and of nonnegative flows along cycles. Dropping the cycles and sending the flow of each path directly from its first vertex to
its last does not raise the cost, by the triangle inequality, and the result, with $\min(S(x), T(x))$ added at each diagonal
entry $(x, x)$, is a coupling of $S$ and $T$ of no larger cost, since $d(x, x) = 0$.

## Expansion

This node states a precise result. A good expansion adds a page for the following prerequisite and links it under the
dependency sections below:

- Proof prerequisite: the decomposition of flows with supplies and demands. A nonnegative real flow on a finite directed graph
  whose net outflow at each vertex $x$ is $b(x)$ is a sum of nonnegative flows along paths, each from a vertex with $b > 0$ to a
  vertex with $b < 0$, and of nonnegative flows along cycles, where the paths starting at a vertex $x$ with $b(x) > 0$ carry
  $b(x)$ in total and no path ends there. The
  [path decomposition of integral flows](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/flow-decompositions-separators-and-chain-covers/flow-path-decomposition.md)
  covers integral flows between two vertices only.

## Depends on

- [Coupling of two weight vectors](../../../Probability/not-yet-classified/part-17/finite-transport/is-coupling.md)
- [Earthmover value](../../../Probability/not-yet-classified/part-17/finite-transport/earthmover.md)

## Sources

- C. Dwork, M. Hardt, T. Pitassi, O. Reingold and R. Zemel, *Fairness through awareness*, ITCS 2012, Definition 3.3 and Lemma 3.2, which the paper calls standard and states without proof. <https://www.cs.toronto.edu/~zemel/documents/fairAwareItcs2012.pdf>
- G. Peyré and M. Cuturi, *Computational Optimal Transport*, Foundations and Trends in Machine Learning 11 (2019), 355–607; arXiv:1803.00567, §6.3, equation (6.6), the Beckmann formulation of $W_1$ on a graph with its geodesic distance. For the complete graph on $V$ with arc lengths $d(x, y)$, the geodesic distance is $d$ itself, since $d$ is a metric. <https://arxiv.org/abs/1803.00567>
