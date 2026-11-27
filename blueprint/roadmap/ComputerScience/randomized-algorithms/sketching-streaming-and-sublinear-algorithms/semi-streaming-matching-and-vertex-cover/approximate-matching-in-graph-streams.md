# Approximate maximum matching and vertex cover in a graph stream

For a simple undirected graph $G = (V, E)$ let $\mu(G)$ be the maximum cardinality of a matching of $G$ and $\tau(G)$ the minimum cardinality of a vertex cover. For $0 < \alpha \le 1$, a streaming algorithm in one of the stream models of the semi-streaming graph model *$\alpha$-approximates maximum matching* if, on every input stream, it outputs a set $M \subseteq E$ that is a matching of $G$ with

$$
|M| \ge \alpha \, \mu(G)
$$

with probability at least $2/3$ (or with high probability, when so stated); a $(1 + \varepsilon)$-approximation means $|M| \ge \mu(G)/(1 + \varepsilon)$. For $\beta \ge 1$ it *$\beta$-approximates minimum vertex cover* if it outputs a vertex cover $C$ of $G$ with $|C| \le \beta \, \tau(G)$.

## Depends on

- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](semi-streaming-graph-model.md)
- [Approximation algorithms and approximation ratios](../../../approximation-algorithms/approximation-algorithms-and-approximation-ratios.md)
- [The augmenting-path maximum matching](../../../graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/max-matching.md)

## Sources

- Michael Kapralov, "Better bounds for matchings in the streaming model", SODA (2013), arXiv:1206.2269.
- Christian Konrad, Frédéric Magniez, Claire Mathieu, "Maximum Matching in Semi-Streaming with Few Passes", APPROX (2012), arXiv:1112.0184.
