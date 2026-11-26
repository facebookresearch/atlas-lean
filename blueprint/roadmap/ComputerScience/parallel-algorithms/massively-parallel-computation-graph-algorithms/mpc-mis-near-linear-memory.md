# MIS in O(log log Delta) MPC rounds with near-linear memory

In the MPC model with local memory $S = \tilde O(n)$, a maximal independent set of an $n$-vertex graph with maximum degree $\Delta$ can be computed by a randomized algorithm in $O(\log\log \Delta)$ rounds with high probability, and the same round complexity applies to maximal matching and $(2 + \varepsilon)$-approximate vertex cover in this memory regime.

## Proof sketch

Simulate the randomized greedy MIS process (processing vertices in a random order) in phases: in each phase, the vertices with the highest remaining priorities induce a subgraph with $O(n)$ edges with high probability, which fits on one machine and is processed sequentially; removing decided vertices reduces the maximum degree of the remainder from $\Delta$ to about $\sqrt\Delta$. Hence $O(\log\log\Delta)$ phases suffice, each costing $O(1)$ MPC rounds.

## Depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)

## Proof depends on

- [MPC with linear memory simulates the congested clique](mpc-simulates-congested-clique.md)

## Sources

- M. Ghaffari, T. Gouleakis, C. Konrad, S. Mitrović, R. Rubinfeld, "Improved Massively Parallel Computation Algorithms for MIS, Matching, and Vertex Cover", PODC 2018, arXiv:1802.08237.
