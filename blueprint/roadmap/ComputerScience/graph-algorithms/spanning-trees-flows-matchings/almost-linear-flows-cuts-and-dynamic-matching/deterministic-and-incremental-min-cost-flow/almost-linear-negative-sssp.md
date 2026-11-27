# Negative-weight single-source shortest paths and negative cycle detection in almost-linear time

There is a deterministic algorithm that, given a directed graph with $m$ edges, integral edge weights in $[-W, W]$ and a source $s$, in time $m^{1+o(1)}\log W$ either computes the distances from $s$ to all vertices or returns a directed cycle of negative total weight. For comparison, a combinatorial randomized algorithm achieves $O(m\log^8 n\log W)$ time.

## Proof sketch

For shortest paths, set lower capacities $0$, upper capacities $n$, costs equal to the weights, demand $n - 1$ leaving $s$ and $1$ arriving at every other vertex, and solve by *Deterministic minimum-cost flow in almost-linear time*; when no negative cycle exists, an optimal flow decomposes into shortest paths from $s$ and its support contains a shortest-path tree, from which the distances follow. For negative cycles, use upper capacities $1$ and zero demands: the optimal circulation is nonzero exactly when a negative cycle exists, and a cycle is extracted from its support with dynamic trees. This matches the classical characterization by Bellman-Ford.

## Depends on

- [Negative-weight single-source shortest paths with integer weights bounded below by -W](../../../shortest-paths/near-linear-negative-weight-sssp/negative-weight-sssp-integer-weights.md)

## Proof depends on

- [Deterministic minimum-cost flow in almost-linear time](deterministic-almost-linear-min-cost-flow.md)
- [Optimality conditions for minimum-cost flows](../../../linear-programming-and-flows/optimality-conditions-for-minimum-cost-flows.md)
- [Link-cut trees take logarithmic amortized time](../../../../data-structures/disjoint-sets-and-dynamic-trees/link-cut-tree/link-cut-trees-take-logarithmic-amortized-time.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
