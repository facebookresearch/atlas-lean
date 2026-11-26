# Edge-degree constrained subgraphs (EDCS)

Let $G = (V, E)$ be a graph and let $\beta > \beta^{-} \ge 1$ be integers. A subgraph $H = (V, E_H)$, $E_H \subseteq E$, is a *$(\beta, \beta^{-})$-edge-degree constrained subgraph* of $G$, written $H = \mathrm{EDCS}(G, \beta, \beta^{-})$, if

1. (P1) $\deg_H(u) + \deg_H(v) \le \beta$ for every edge $\{u, v\} \in E_H$;
2. (P2) $\deg_H(u) + \deg_H(v) \ge \beta^{-}$ for every edge $\{u, v\} \in E \setminus E_H$.

Property (P1) forces sparsity and (P2) forces every non-chosen edge to be well covered by the chosen ones.

## Depends on

- [Fully dynamic alpha-approximate maximum matching and its value version](dynamic-approximate-matching-problem.md)

## Sources

- Aaron Bernstein, Cliff Stein, "Fully Dynamic Matching in Bipartite Graphs", ICALP (2015), arXiv:1506.07076.
- Aaron Bernstein, Cliff Stein, "Faster Fully Dynamic Matchings with Small Approximation Ratios", SODA (2016).
- Sepehr Assadi, Aaron Bernstein, "Towards a Unified Theory of Sparsification for Matching Problems", SOSA (2019), arXiv:1811.02009.
