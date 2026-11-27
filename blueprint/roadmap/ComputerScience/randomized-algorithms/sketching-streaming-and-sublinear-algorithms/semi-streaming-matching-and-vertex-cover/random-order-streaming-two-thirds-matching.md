# Bernstein's (2/3 - eps)-approximate matching in random-order semi-streams

For every graph $G$ on $n$ vertices (not necessarily bipartite) and every $0 < \varepsilon < 1$ there is a deterministic single-pass streaming algorithm that, when the edges of $G$ arrive in a uniformly random order, outputs with high probability (over the order) a matching of size at least $(2/3 - \varepsilon)\,\mu(G)$, using

$$
O\big(n \log n \cdot \mathrm{poly}(1/\varepsilon)\big)
$$

bits of space.

## Proof sketch

Phase I reads an initial portion of the stream and maintains a subgraph $H$ of bounded edge-degree $\beta = \mathrm{poly}(1/\varepsilon)$, inserting underfull edges and deleting overfull ones, until a whole stage passes with few changes; random order makes the processed prefix a uniform sample, so $H$ is then close to an EDCS of the full graph. Phase II stores every remaining edge that is underfull with respect to $H$; a random-order concentration argument bounds their number by $O(n \log n \cdot \mathrm{poly}(1/\varepsilon))$. A variant of the EDCS matching lemma shows $\mu(H \cup X) \ge (2/3 - \varepsilon)\mu(G)$ for the stored set $X$, and the algorithm outputs a maximum matching of $H \cup X$.

## Depends on

- [Approximate maximum matching and vertex cover in a graph stream](approximate-matching-in-graph-streams.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](semi-streaming-graph-model.md)

## Proof depends on

- [Every graph contains a (beta, beta^-)-EDCS, and it has O(n beta) edges](../../../graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/dynamic-matching-against-adaptive-adversaries/edcs-existence-and-sparsity.md)
- [An EDCS contains an almost 3/2-approximate maximum matching](../../../graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/dynamic-matching-against-adaptive-adversaries/edcs-three-halves-approximation.md)
- [Edge-degree constrained subgraphs (EDCS)](../../../graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/dynamic-matching-against-adaptive-adversaries/edge-degree-constrained-subgraph.md)

## Sources

- Aaron Bernstein, "Improved Bounds for Matching in Random-Order Streams", ICALP (2020), arXiv:2005.00417.
- Sepehr Assadi, Aaron Bernstein, "Towards a Unified Theory of Sparsification for Matching Problems", SOSA (2019), arXiv:1811.02009.
