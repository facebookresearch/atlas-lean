# Linear list-chromatic bound in clique-minor order

There is a natural $C\ge1$ such that every nonempty finite simple graph $G$ satisfies $\chi_{\mathrm{list}}(G)\le C h(G)$. Here $\chi_{\mathrm{list}}$ is the least $k$ for which, for every color type and every assignment of finite lists of size at least $k$, a proper coloring can pick a color from each vertex's own list. The number $h(G)$ is the greatest number of disjoint connected branch sets with inter-set edges between every pair.

## Depends on

- List chromatic number with arbitrary color type, and order of a largest clique minor.

## Expansion

Separate the exact finite-list structural reduction to the weighted obstruction and the exclusion of the obstruction for every induced subgraph. The latter uses the separate fractional weighted bound, not a previously proved linear list-colouring result. Then use the source alternative to obtain a uniform integer constant.

## Proof outline

Bridge the existing graph colouring and minor APIs to finite-list colourability and branch sets. Check that the set of admissible k is nonempty and the clique-minor order finite before taking extrema. Separate proof into the structural graph estimates and the resulting list-coloring bound.

## Sources

- [Comparator statement: `OAI.LinearListHadwiger.main_theorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ListHadwiger.lean#L30-L32)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/157.md)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/ListHadwiger/Main.lean)
