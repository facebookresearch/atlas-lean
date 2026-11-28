# Contractions preserving all non-trivial minimum cuts of a simple graph

Let $G = (V, E)$ be a simple connected undirected graph with minimum degree $\delta$ and edge connectivity $\lambda \le \delta$. A global minimum cut $S$ is *non-trivial* if $|S| \ge 2$ and $|V \setminus S| \ge 2$. A partition $\mathcal{Q}$ of $V$ *preserves all non-trivial minimum cuts* if every part $Q \in \mathcal{Q}$ satisfies $Q \subseteq S$ or $Q \subseteq V \setminus S$ for every non-trivial minimum cut $S$. The multigraph $G / \mathcal{Q}$ obtained by contracting each part to a vertex and deleting loops keeps parallel edges; every non-trivial minimum cut of $G$ is then a cut of $G / \mathcal{Q}$ of the same size.

## Depends on

- [Minimum cut size](../../../../randomized-algorithms/karger-s-algorithm/is-min-cut.md)
- [Edge contraction](../../../../randomized-algorithms/karger-s-algorithm/contract.md)
- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Sources

- Ken-ichi Kawarabayashi, Mikkel Thorup, "Deterministic Edge Connectivity in Near-Linear Time", STOC (2015) and Journal of the ACM (2019), arXiv:1411.5123.
- On-Hei Solomon Lo, Jens M. Schmidt, Mikkel Thorup, "Compact Cactus Representations of all Non-Trivial Min-Cuts", Discrete Applied Mathematics (2020), arXiv:1810.03865.
