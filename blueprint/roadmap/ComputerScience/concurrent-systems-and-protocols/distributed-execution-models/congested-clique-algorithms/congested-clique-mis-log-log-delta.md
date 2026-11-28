# Maximal independent set in O(log Delta log log Delta / sqrt(log n) + log log Delta) rounds of the congested clique

In the congested clique, a maximal independent set of an $n$-vertex input graph of maximum degree $\Delta$ can be computed by a randomized algorithm in

$$
O\!\left(\frac{\log\Delta \cdot \log\log\Delta}{\sqrt{\log n}} + \log\log\Delta\right)
$$

rounds with high probability. In particular, for low-degree graphs with $\Delta \le 2^{O(\sqrt{\log n})}$ the bound is $O(\log\log \Delta)$ rounds, and for general $\Delta$ it is $\tilde O(\sqrt{\log \Delta})$.

## Proof sketch

Start from a sparsified variant of Ghaffari's beeping-based LOCAL MIS algorithm, whose $O(\log \Delta)$ rounds are grouped into phases of $\Theta(\sqrt{\log n})$ rounds each; within a phase, every node's random decisions depend only on a sampled subgraph of small degree. Each phase is simulated in $O(\log\log\Delta)$ rounds of the congested clique: nodes learn their sampled multi-hop neighbourhoods by repeated graph exponentiation using Lenzen routing, and then simulate the phase locally. This gives $O(\log\Delta \cdot \log\log\Delta/\sqrt{\log n})$ rounds when $\log\log\Delta = \Theta(\log\log n)$; in the complementary low-degree case a simpler variant of the same simulation takes $O(\log\log\Delta)$ rounds. With high probability the remaining graph has $O(n)$ edges, so it is collected at one node and solved in $O(1)$ further rounds.

## Depends on

- [The congested clique model](the-congested-clique-model.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)
- [Randomized MIS in O(log Delta) + polylog-size deterministic time](../../local-distributed-algorithms/deterministic-colouring-and-mis-in-local-and-congest/randomized-mis-log-delta-shattering.md)

## Sources

- M. Ghaffari, "Distributed MIS via All-to-All Communication", PODC 2017, Theorem 1.1, Section 2.4 and Lemma 2.15.
