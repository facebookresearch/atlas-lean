# Weighted connectivity augmentation problem (WCAP)

Let $k \ge 1$ and let $G=(V,E)$ be a $k$-edge-connected undirected multigraph, so that by Menger's theorem every pair of vertices is joined by $k$ edge-disjoint paths. Given links $L \subseteq \binom{V}{2}$ with weights $w:L \to \mathbb{R}_{> 0}$, the weighted connectivity augmentation problem asks for

$$
\min\{w(F) : F \subseteq L,\ (V,E \uplus F)\ \text{is}\ (k+1)\text{-edge-connected}\},
$$

where edges of $G$ and links keep distinct identities and $E \uplus F$ is the disjoint union, a multigraph in which a link parallel to an edge of $G$ adds a new parallel edge.

Equivalently $F$ must contain a link crossing every minimum cut $\delta_G(S)$ with $|\delta_G(S)|=k$: in the disjoint union every cut $\delta(S)$ gains one edge per link of $F$ crossing it. The case $w \equiv 1$ is the connectivity augmentation problem (CAP); the case $k=1$ is WTAP after contracting 2-edge-connected components.

## Depends on

- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Minimum cut size](../../../randomized-algorithms/karger-s-algorithm/is-min-cut.md)

## Sources

- Federica Cecchetto, Vera Traub, Rico Zenklusen, "Bridging the Gap Between Tree and Connectivity Augmentation: Unified and Stronger Approaches", STOC (2021), arXiv:2012.00086.
- Vera Traub, Rico Zenklusen, "A (1.5+epsilon)-Approximation Algorithm for Weighted Connectivity Augmentation", STOC (2023), arXiv:2209.07860.
