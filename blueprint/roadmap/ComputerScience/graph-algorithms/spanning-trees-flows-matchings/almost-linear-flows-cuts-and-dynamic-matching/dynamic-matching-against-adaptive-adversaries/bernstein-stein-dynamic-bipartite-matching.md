# Bernstein-Stein: deterministic (3/2+eps)-approximate bipartite matching in O(m^{1/4} eps^{-2.5}) worst-case time

For every $0 < \varepsilon < 2/3$ there is a deterministic fully dynamic algorithm that maintains a $(3/2 + \varepsilon)$-approximate maximum matching in a bipartite graph with $m$ edges in worst-case update time $O(m^{1/4}\varepsilon^{-2.5})$. For bipartite graphs of arboricity at most $\alpha$ and constant $\varepsilon$, a $(1 + \varepsilon)$-approximate matching can be maintained in worst-case update time $O(\alpha(\alpha + \log n))$. Being deterministic, these work against adaptive adversaries.

## Proof sketch

Maintain an EDCS $H$ with $\beta$ chosen as a function of $m$ and $\varepsilon$: an edge update triggers a chain of fixes, but a potential argument bounds the amortized number of changes to $H$, and a deamortization keeps the worst case under control. A $(1+\varepsilon)$-approximate matching of the sparse $H$ is recomputed lazily over batches of updates, and $H$ itself loses at most a $3/2 + \varepsilon$ factor. Balancing the cost of maintaining $H$ against the rebuild cost gives $O(m^{1/4}\varepsilon^{-2.5})$.

## Depends on

- [Oblivious and adaptive adversaries; amortized and worst-case update time](../../../../data-structures/disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/adversary-and-update-time-models.md)
- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)

## Proof depends on

- [Every graph contains a (beta, beta^-)-EDCS, and it has O(n beta) edges](edcs-existence-and-sparsity.md)
- [An EDCS contains an almost 3/2-approximate maximum matching](edcs-three-halves-approximation.md)

## Sources

- Aaron Bernstein, Cliff Stein, "Fully Dynamic Matching in Bipartite Graphs", ICALP (2015), arXiv:1506.07076, Theorem 1.
- Aaron Bernstein, Cliff Stein, "Faster Fully Dynamic Matchings with Small Approximation Ratios", SODA (2016).
