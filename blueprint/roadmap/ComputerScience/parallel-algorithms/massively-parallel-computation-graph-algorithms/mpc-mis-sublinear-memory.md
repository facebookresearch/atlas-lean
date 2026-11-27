# MIS in O(sqrt(log Delta) log log Delta + sqrt(log log n)) MPC rounds with sublinear memory

In the MPC model with strongly sublinear local memory $S = n^{\alpha}$ for any constant $\alpha \in (0, 1)$ and total memory $\tilde O(m)$, a maximal independent set of an $n$-vertex graph with maximum degree $\Delta$ can be computed by a randomized algorithm in $\tilde O(\sqrt{\log \Delta}) + O(\sqrt{\log\log n})$ rounds with high probability.

## Proof sketch

Sparsify the LOCAL desire-level MIS algorithm: run it in phases of $R = O(\sqrt{\log \Delta})$ rounds, and show that each phase can be simulated on a sparse subgraph of degree $2^{O(\sqrt{\log\Delta})}$, in which each vertex's behaviour during the phase depends on only $\Delta^{O(1)}$ vertices and edges (its locality volume), small enough to gather on one machine by graph exponentiation in $O(\log R) = O(\log\log\Delta)$ rounds. Simulating each phase in $O(\log R)$ MPC rounds yields $O(\sqrt{\log\Delta} \cdot \log\log\Delta)$ rounds, followed by shattering and a deterministic finish.

## Depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)

## Proof depends on

- [The LOCAL model](../../concurrent-systems-and-protocols/distributed-execution-models/the-local-model.md)
- [Randomized MIS in O(log Delta) + polylog-size deterministic time](../../concurrent-systems-and-protocols/local-distributed-algorithms/deterministic-colouring-and-mis-in-local-and-congest/randomized-mis-log-delta-shattering.md)
- [Graph shattering after a randomized pre-shattering phase](../../concurrent-systems-and-protocols/local-distributed-algorithms/deterministic-colouring-and-mis-in-local-and-congest/graph-shattering-lemma.md)

## Sources

- M. Ghaffari, J. Uitto, "Sparsifying Distributed Algorithms with Ramifications in Massively Parallel Computation and Centralized Local Computation", SODA 2019, arXiv:1807.06251.
