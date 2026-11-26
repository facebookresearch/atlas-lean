# MIS in O(log log Delta) MPC rounds with near-linear memory

In the MPC model with local memory $S = \tilde O(n)$, a maximal independent set of an $n$-vertex graph with maximum degree $\Delta$ can be computed by a randomized algorithm in $O(\log\log \Delta)$ rounds with high probability, and, with the same memory, a $(2 + \varepsilon)$-approximate maximum matching and a $(2 + \varepsilon)$-approximate minimum vertex cover can be computed in $O(\log\log n)$ rounds.

## Proof sketch

Simulate the randomized greedy MIS process (processing vertices in a uniformly random order $\pi$) on prefixes of the order. In iteration $i$, the remaining vertices with ranks between $n/\Delta^{\alpha^{i-1}}$ and $n/\Delta^{\alpha^i}$, for $\alpha = 3/4$, induce a subgraph with $O(n)$ edges with high probability; it is sent to one machine, which runs the greedy process on it, and every machine then removes the new MIS vertices and their neighbours. After $O(\log\log\Delta)$ iterations the next rank reaches $n/\log^{10} n$, and the residual graph has maximum degree $\Delta' = O(\log^{11} n)$ with high probability. This does not yet bound its number of edges, and the greedy phases have not finished. Next, run $O(\log\log\Delta')$ rounds of Ghaffari's sparsified MIS algorithm for low-degree graphs, which applies when $\Delta' \le 2^{O(\sqrt{\log n})}$ and makes only simple local decisions, so each of its rounds takes $O(1)$ MPC rounds with $\tilde O(n)$ memory per machine. Remove the independent set it constructs together with its neighbourhood; with high probability the remaining graph has $O(n)$ edges. Finally collect the remaining graph on one machine, compute an MIS of it there in one round, and output the union of the sets found. The round count is $O(\log\log\Delta)$ in total.

## Depends on

- [The massively parallel computation model](massively-parallel-computation-model.md)

## Proof depends on

- [Maximal independent set in O(log Delta log log Delta / sqrt(log n) + log log Delta) rounds of the congested clique](../../concurrent-systems-and-protocols/distributed-execution-models/congested-clique-algorithms/congested-clique-mis-log-log-delta.md)

## Sources

- M. Ghaffari, T. Gouleakis, C. Konrad, S. Mitrović, R. Rubinfeld, "Improved Massively Parallel Computation Algorithms for MIS, Matching, and Vertex Cover", PODC 2018, arXiv:1802.08237, Sections 3.1–3.3 (Lemma 3.1).
- M. Ghaffari, "Distributed MIS via All-to-All Communication", PODC 2017, Theorem 1.1.
