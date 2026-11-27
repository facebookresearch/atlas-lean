# Beating two-thirds for random-order streaming matching

There is an absolute constant $\varepsilon_0 > 0$ such that for every $n$-vertex graph $G$ whose edges arrive in a uniformly random order, a single-pass streaming algorithm using $O(n \log n)$ words of $\Theta(\log n)$ bits outputs, with high probability, a matching of size at least

$$
\Big(\frac{2}{3} + \varepsilon_0\Big)\mu(G).
$$

This breaks the factor $2/3$ reached by all earlier random-order algorithms, including those that keep an edge-degree constrained subgraph (EDCS), which always contains an almost $2/3$-approximate matching.

## Proof sketch

Run Bernstein's algorithm, which builds in the first $o(1)$ fraction of the stream a subgraph $H$ of bounded edge-degree and then stores the underfull edges of the rest. A structural characterization of the EDCS-type subgraphs that fail to beat $2/3$ shows that the algorithm can fail only if $H$ already contains an almost $2/3$-approximate matching $M$ after that first $o(1)$ fraction. In that case $M$ has essentially no augmenting paths of length three, and the remainder of the stream is used to find length-five augmenting paths: a path is *discoverable* when its middle edge arrives after its two end edges, a constant fraction of the paths are discoverable because the order is random, and a procedure within the same $O(n\log n)$ space finds a constant fraction of the discoverable ones. Taking the better of the two outcomes gains an absolute constant $\varepsilon_0$.

## Depends on

- [Approximate maximum matching and vertex cover in a graph stream](approximate-matching-in-graph-streams.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](semi-streaming-graph-model.md)
- [Edge-degree constrained subgraphs (EDCS)](../../../graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/dynamic-matching-against-adaptive-adversaries/edge-degree-constrained-subgraph.md)

## Proof depends on

- [Bernstein's (2/3 - eps)-approximate matching in random-order semi-streams](random-order-streaming-two-thirds-matching.md)
- [Every graph contains a (beta, beta^-)-EDCS, and it has O(n beta) edges](../../../graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/dynamic-matching-against-adaptive-adversaries/edcs-existence-and-sparsity.md)
- [An EDCS contains an almost 3/2-approximate maximum matching](../../../graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/dynamic-matching-against-adaptive-adversaries/edcs-three-halves-approximation.md)
- [Augmenting path](../../../../GraphTheory/matchings-and-flows/berge-s-lemma/is-augmenting-walk.md)

## Sources

- Sepehr Assadi, Soheil Behnezhad, "Beating Two-Thirds For Random-Order Streaming Matching", ICALP (2021), arXiv:2102.07011.
