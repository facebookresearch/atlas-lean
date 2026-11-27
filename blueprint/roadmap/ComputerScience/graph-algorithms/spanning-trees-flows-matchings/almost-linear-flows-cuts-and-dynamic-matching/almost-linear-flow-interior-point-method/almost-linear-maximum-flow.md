# Maximum flow in almost-linear time with a logarithmic dependence on capacities

There is a randomized algorithm that, on a directed graph with $m$ edges, integral capacities in $[1, U]$ and two vertices $s \ne t$, computes a maximum $s$-$t$ flow and a minimum $s$-$t$ cut in time $m^{1+o(1)}\log U$ with high probability.

## Proof sketch

Apply *Minimum-cost flow in almost-linear time with high probability* to the circulation instance of *Integral minimum-cost flow instances with polynomially bounded data* with one arc $(t, s)$ of cost $-1$; there $C = 1$, so the bound becomes $m^{1+o(1)}\log U$, and the optimal circulation restricted to $G$ is a maximum flow. A minimum cut is read off as the set of vertices reachable from $s$ in the residual graph, whose capacity equals the flow value by the max-flow min-cut theorem.

## Depends on

- [Flow value](../../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/flow-value.md)
- [Cut capacity](../../edmonds-karp-algorithm/cut-capacity.md)

## Proof depends on

- [Minimum-cost flow in almost-linear time with high probability](almost-linear-min-cost-flow.md)
- [Max-flow min-cut theorem](../../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)
- [Edmonds-Karp computes a maximum flow and a minimum cut](../../edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)
- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
