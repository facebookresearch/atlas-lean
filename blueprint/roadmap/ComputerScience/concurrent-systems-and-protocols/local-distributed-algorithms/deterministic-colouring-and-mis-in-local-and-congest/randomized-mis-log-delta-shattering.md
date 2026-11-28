# Randomized MIS in O(log Delta) + polylog-size deterministic time

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. There is a randomized LOCAL algorithm for maximal independent set running in $O(\log \Delta) + 2^{O(\sqrt{\log\log n})}$ rounds with high probability; with polylogarithmic deterministic network decompositions the additive term becomes $\mathrm{poly}(\log\log n)$. Moreover each vertex individually terminates within $O(\log \deg(v) + \log(1/\varepsilon))$ rounds with probability at least $1 - \varepsilon$.

## Proof sketch

Each vertex maintains a desire level $p_t(v)$, starts at $1/2$, halves it when the sum of its neighbours' desire levels is at least $2$ and doubles it (up to $1/2$) otherwise, and marks itself with probability $p_t(v)$, joining the MIS if no neighbour is marked. A potential argument shows that within $O(\log \Delta + \log(1/\varepsilon))$ rounds each vertex has, with probability $1 - \varepsilon$, many golden rounds in which it or a neighbour is likely to join. Graph shattering then leaves small components solved deterministically.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [Network decomposition with weak or strong diameter](../deterministic-network-decomposition/network-decomposition-weak-strong-diameter.md)

## Proof depends on

- [Graph shattering after a randomized pre-shattering phase](graph-shattering-lemma.md)
- [Polylogarithmic-time deterministic network decomposition](../deterministic-network-decomposition/polylogarithmic-deterministic-network-decomposition.md)

## Sources

- M. Ghaffari, "An Improved Distributed Algorithm for Maximal Independent Set", SODA 2016, arXiv:1506.05093.
