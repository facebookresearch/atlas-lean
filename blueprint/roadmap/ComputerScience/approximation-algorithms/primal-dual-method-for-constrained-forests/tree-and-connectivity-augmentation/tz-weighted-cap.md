# Traub-Zenklusen: weighted connectivity augmentation is (1.5 + eps)-approximable

For every fixed $\varepsilon > 0$ there is a polynomial-time $(1.5+\varepsilon)$-approximation algorithm for the weighted connectivity augmentation problem, for every $k \ge 1$ and without any bound on the link weights. Before this result no approximation factor below $2$ was known for WCAP with even $k$.

## Proof sketch

Weaken WCAP to a directed covering problem on the cactus of minimum cuts, and show that this directed weakening has solutions with a planar structure. Interpreting WCAP solutions as solutions to the weakening, local exchange steps are described within a component class related to bounded-treewidth subgraphs of circle graphs, over which the best step is computable. A decomposition theorem for optimal solutions into such components then gives the $(1.5+\varepsilon)$ guarantee exactly as in the local search analysis for WTAP.

## Depends on

- [Weighted connectivity augmentation problem (WCAP)](connectivity-augmentation.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Augmenting odd edge-connectivity reduces to tree augmentation](odd-cap-reduces-to-tap.md)
- [Traub-Zenklusen local search: weighted tree augmentation is (1.5 + eps)-approximable](tz-local-search-wtap.md)
- [Cactus representations of all minimum cuts](../../../../GraphTheory/paths-cycles-connectivity/cactus-representation-and-sparse-certificates/cactus-representation-of-minimum-cuts.md)

## Sources

- Vera Traub, Rico Zenklusen, "A (1.5+epsilon)-Approximation Algorithm for Weighted Connectivity Augmentation", STOC (2023), arXiv:2209.07860.
