# Quantitative counterexample for two-degenerate bipartite graphs

There is a
connected bipartite $2$-degenerate finite simple graph $H$ such that for every
proper coloring with two colors, each color class contains a vertex of degree
at least three in $H$. For one such $H$ there are real $c,\varepsilon>0$ such
that $\operatorname{ex}(n;H)\ge c n^{3/2+\varepsilon}$ for every sufficiently
large natural number $n$. The extremal number counts edges in an $n$-vertex
simple graph with no subgraph isomorphic to $H$.

## Depends on

- [Extremal number for one forbidden graph](../extremal-number-for-one-forbidden-graph.md)
- [Degenerate graph](../../graph-coloring/part-01/degeneracy-and-greedy-coloring/is-degenerate.md)

## Proof depends on

- [Pair-layer graphs](pair-layer-graphs.md)
- [Extremal lower bound for pair-layer graphs along Hamming sampling orders](sampled-hamming-hosts-excluding-pair-layer-graphs.md)
- [Extremal lower bounds between sampled orders](extremal-lower-bounds-between-sampled-orders.md)

## Proof outline

Use one pair-layer graph from the sampled-order estimate. Check its connectivity, two-degeneracy and degree condition in both color classes. The source upper-bounds consecutive sample orders by a factor of two. Transfer the sampled bound to all sufficiently large orders by padding with isolated vertices in the host.

## Sources

- OpenAI, [*Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 10](https://cdn.openai.com/pdf/ten-proofs-oai.pdf), [pinned quantitative formulation](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ComparatorChallenges/J_TwoDegenerateGraphs.lean#L28-L40).
- [Source witness and order transfer](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L18441-L18541)
