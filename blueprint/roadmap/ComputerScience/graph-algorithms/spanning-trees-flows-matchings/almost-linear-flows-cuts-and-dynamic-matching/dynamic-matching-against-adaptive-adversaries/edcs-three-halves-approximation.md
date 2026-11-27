# An EDCS contains an almost 3/2-approximate maximum matching

Let $\varepsilon < 1/2$.

1. If $G$ is bipartite, $\lambda \le \varepsilon/4$, $\beta \ge 2\lambda^{-1}$ and $\beta^{-} \ge (1 - \lambda)\beta$, then every $H = \mathrm{EDCS}(G, \beta, \beta^{-})$ satisfies $\mu(G) \le (3/2 + \varepsilon)\,\mu(H)$.
2. For general $G$, if $\lambda \le \varepsilon/32$, $\beta \ge 8\lambda^{-2}\log(1/\lambda)$ and $\beta^{-} \ge (1 - \lambda)\beta$, then every $H = \mathrm{EDCS}(G, \beta, \beta^{-})$ satisfies $\mu(G) \le (3/2 + \varepsilon)\,\mu(H)$.

In both cases $H$ has $O(n\beta) = O_{\varepsilon}(n)$ edges, so an EDCS is a sparse, update-robust matching sparsifier.

## Proof sketch

In the bipartite case take a witness set $A$ of the extended Hall theorem for $H$, so that $\mu(H) = n - (|A| - |N_H(A)|)$, and compare with a maximum matching of $G$. Edges of $G$ leaving $A$ outside $N_H(A)$ are missing from $H$, so by (P2) their endpoints have large total $H$-degree, while (P1) caps degrees inside $H$; double counting $H$-degrees across $A$ and $N_H(A)$ gives the $3/2 + \varepsilon$ bound. The general case reduces to the bipartite one: randomly orient a maximum matching of $G$ into a bipartition, and use the Lovász Local Lemma to show the restricted $H$ is still an EDCS of the bipartite subgraph with slightly perturbed parameters.

## Depends on

- [Edge-degree constrained subgraphs (EDCS)](edge-degree-constrained-subgraph.md)

## Proof depends on

- [Kőnig's theorem for finite bipartite graphs](../../../../../GraphTheory/matchings-and-flows/k-nig-s-theorem/konig-matching-cover.md)
- [Every graph contains a (beta, beta^-)-EDCS, and it has O(n beta) edges](edcs-existence-and-sparsity.md)

## Sources

- Sepehr Assadi, Aaron Bernstein, "Towards a Unified Theory of Sparsification for Matching Problems", SOSA (2019), arXiv:1811.02009.
- Aaron Bernstein, Cliff Stein, "Fully Dynamic Matching in Bipartite Graphs", ICALP (2015), arXiv:1506.07076.
- Aaron Bernstein, Cliff Stein, "Faster Fully Dynamic Matchings with Small Approximation Ratios", SODA (2016).
