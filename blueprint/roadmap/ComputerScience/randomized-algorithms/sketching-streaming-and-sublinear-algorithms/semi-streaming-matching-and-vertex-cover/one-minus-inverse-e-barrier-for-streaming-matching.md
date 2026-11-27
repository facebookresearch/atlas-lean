# No single-pass semi-streaming algorithm beats 1 - 1/e for bipartite matching under vertex arrivals

Let $G = (P \cup Q, E)$ be a bipartite graph with $n$ vertices, presented as a *vertex-arrival stream*: the vertices of $Q$ arrive one at a time in an adversarial order, each together with all its incident edges. For every constant $\delta > 0$, every randomized single-pass streaming algorithm that on every such stream outputs, with probability at least $3/4$, a matching of size at least $(1 - 1/e + \delta)\,\mu(G)$ uses $n^{1 + \Omega_\delta(1/\log\log n)}$ bits of memory, which exceeds $n\log^{c} n$ for every constant $c$ and large $n$.

Listing the edges of each arriving vertex consecutively turns a vertex-arrival stream into an insertion-only edge stream, so the same barrier holds for edge arrivals. The bound is tight in the vertex-arrival model: the Karp–Vazirani–Vazirani ranking algorithm achieves approximation ratio $1 - 1/e$ in expectation with $\widetilde{O}(n)$ space, and a deterministic single-pass algorithm of Goel, Kapralov and Khanna achieves $1 - 1/e$ in $\widetilde{O}(n)$ space.

## Proof sketch

The proof shows a more refined communication bound: if the edges are split among $k$ players who each send one message to the next, no protocol with $n^{1 + o(1/\log\log n)}$ bits of communication achieves approximation $1 - (1 - 1/k)^k + \Omega(1)$, and $1 - (1 - 1/k)^k \to 1 - 1/e$. The hard input consists of $k$ parts, generalizing a two-part construction of Goel, Kapralov and Khanna that gives only $3/4$: host graphs are indexed by tuples of vectors from exponentially large families of nearly orthogonal vectors, following techniques for constructing Ruzsa–Szemerédi graphs, so that each player's part is a dense union of induced matchings and a short message cannot identify the edges that later parts extend. A single-pass streaming algorithm under vertex arrivals yields such a protocol with communication equal to its memory.

## Depends on

- [Approximate maximum matching and vertex cover in a graph stream](approximate-matching-in-graph-streams.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](semi-streaming-graph-model.md)

## Proof depends on

- [Ruzsa-Szemerédi graphs: edge sets partitioned into large induced matchings](ruzsa-szemeredi-graphs.md)
- [Yao's minimax principle](../../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- Michael Kapralov, "Better bounds for matchings in the streaming model", SODA (2013), arXiv:1206.2269.
