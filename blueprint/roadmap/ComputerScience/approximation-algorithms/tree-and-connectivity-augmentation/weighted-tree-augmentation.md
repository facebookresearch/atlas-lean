# Weighted tree augmentation problem (WTAP)

An instance of the weighted tree augmentation problem consists of a spanning tree $G=(V,E)$, a set of links $L \subseteq \binom{V}{2}$ and weights $w:L \to \mathbb{R}_{> 0}$. For a link $\ell=uv$ let $P_\ell \subseteq E$ be the edge set of the unique $u$-$v$ path in $G$; $\ell$ covers the tree edges in $P_\ell$. The task is

$$
\min\Big\{w(F) : F \subseteq L,\ \bigcup_{\ell \in F}P_\ell=E\Big\},
$$

equivalently, a minimum-weight $F$ such that $(V,E \cup F)$ is 2-edge-connected, since each tree edge forms a 1-edge cut. The unweighted case $w \equiv 1$ is the tree augmentation problem (TAP), which is APX-hard. The natural cut LP relaxes $F$ to $y \in \mathbb{R}_{\ge 0}^{L}$ with $\sum_{\ell:\,e \in P_\ell}y_\ell \ge 1$ for all $e \in E$.

## Depends on

- [Edge cuts separating two vertices](../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/is-stedge-cut.md)
- [Menger's theorem for edge cuts and edge-disjoint paths](../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/menger-edge-max-min.md)
- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Sources

- Greg N. Frederickson, Joseph JaJa, "Approximation Algorithms for Several Graph Augmentation Problems", SIAM Journal on Computing (1981).
- Vera Traub, Rico Zenklusen, "A Better-Than-2 Approximation for Weighted Tree Augmentation", FOCS (2021), arXiv:2104.07114.
