# No single-pass semi-streaming algorithm beats 1 - 1/e for bipartite matching under vertex arrivals

Let $G = (P \cup Q, E)$ be bipartite with $|P| = |Q| = n$, presented as a *vertex-arrival stream*: the vertices of $Q$ arrive one at a time in an adversarial order, each together with all its incident edges. For every constant $\delta > 0$ and every constant $c$, for all sufficiently large $n$, every randomized single-pass streaming algorithm that on every such stream outputs, with probability at least $2/3$, a matching of size at least $(1 - 1/e + \delta)\,\mu(G)$ uses more than $n \log^{c} n$ bits of memory.

Listing the edges of each arriving vertex consecutively turns a vertex-arrival stream into an insertion-only edge stream, so the same barrier holds for edge arrivals. The bound is tight in the vertex-arrival model: simulating the Karp–Vazirani–Vazirani ranking algorithm gives expected approximation ratio $1 - 1/e$ with $O(n \log n)$ bits.

## Proof sketch

The hard distribution hides the upper-triangular instances on which online ranking is optimal inside dense Ruzsa–Szemerédi graphs: the early part of the stream is a union of many induced matchings, and only one of them, unknown to the algorithm, is later extended by the arriving vertices. A memory of $n \log^{O(1)} n$ bits can retain only a vanishing fraction of the edges of the hidden induced matching, and an averaging argument over the matchings converts this into an approximation loss that tends to the online bound $1 - 1/e$.

## Depends on

- [Approximate maximum matching and vertex cover in a graph stream](approximate-matching-in-graph-streams.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](semi-streaming-graph-model.md)

## Proof depends on

- [Ruzsa-Szemerédi graphs: edge sets partitioned into large induced matchings](ruzsa-szemeredi-graphs.md)
- [Dense bipartite Ruzsa-Szemerédi graphs from Behrend's progression-free sets](ruzsa-szemeredi-graphs-from-behrend-sets.md)
- [Yao's minimax principle](../../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- Michael Kapralov, "Better bounds for matchings in the streaming model", SODA (2013), arXiv:1206.2269.
