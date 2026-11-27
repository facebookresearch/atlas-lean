# Beating two-thirds for random-order streaming matching

There is an absolute constant $\varepsilon_0 > 0$ such that for every $n$-vertex graph $G$ whose edges arrive in a uniformly random order, a single-pass streaming algorithm using $O(n \log n)$ space outputs, with high probability, a matching of size at least

$$
\Big(\frac{2}{3} + \varepsilon_0\Big)\mu(G).
$$

This breaks the factor $2/3$ that is the limit of every EDCS-based approach, since there are graphs and EDCSs $H$ with $\mu(H)$ arbitrarily close to $\frac{2}{3}\mu(G)$.

## Proof sketch

Run the EDCS-based random-order algorithm and analyze the instances on which it returns only about $\frac{2}{3}\mu(G)$: in those, the maximum matching interacts with the EDCS in a rigid structure, with most edges of an optimal matching forming length-three augmenting paths through $H$. The remaining part of the stream, which is a uniform sample of the edges, then contains many disjoint short augmenting paths, and a second procedure that stores few extra edges per vertex finds a constant fraction of them; taking the better of the two outcomes gains an absolute constant $\varepsilon_0$.

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
