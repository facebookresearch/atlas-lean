# Cecchetto-Traub-Zenklusen: unweighted connectivity augmentation is 1.393-approximable

There is a polynomial-time $1.393$-approximation algorithm for the (unweighted) connectivity augmentation problem, for every $k \ge 1$; in particular also for TAP. This improves the factor $1.91$ for CAP of Byrka, Grandoni and Jabal Ameli and the factor $1.458$ for TAP of Grandoni, Kalaitzis and Zenklusen. Moreover, when the ratio between the largest and smallest link weight is bounded by a constant, the same approach yields approximation factors below $1.5$ for the weighted problems.

## Proof sketch

CAP reduces to cactus augmentation (CacAP). First, a black-box reduction in the spirit of Adjiashvili shows that an $\alpha$-approximation for $k$-wide instances, in which every component of the cactus minus a center vertex $r$ contains at most $k$ degree-two vertices (terminals), gives an $\alpha(1+\varepsilon)$-approximation in general for a suitable constant $k=k(\varepsilon)$ (Theorem 5); it splits instances at light cuts and covers heavy cuts by a rectangle hitting problem (Sections 3–4). On $k$-wide instances, links are classified as cross-links between principal subcacti and in-links, and two backbone procedures are combined by returning the better solution: one rounds the cross-links using Chvátal–Gomory cuts after bidirecting links (Section 5), the other rounds an LP relaxation over $L_{\mathrm{cross}}$-minimal solutions and removes redundant links (Section 6). Their combination already gives $1.5$; the stack analysis of Section 6, which bounds the expected number of removable links, improves the second procedure and yields $1.393$.

## Depends on

- [Weighted connectivity augmentation problem (WCAP)](connectivity-augmentation.md)
- [Weighted tree augmentation problem (WTAP)](weighted-tree-augmentation.md)
- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Augmenting odd edge-connectivity reduces to tree augmentation](odd-cap-reduces-to-tap.md)
- [Cactus representations of all minimum cuts](../../../GraphTheory/paths-cycles-connectivity/cactus-representation-and-sparse-certificates/cactus-representation-of-minimum-cuts.md)

## Sources

- Federica Cecchetto, Vera Traub, Rico Zenklusen, "Bridging the Gap Between Tree and Connectivity Augmentation: Unified and Stronger Approaches", STOC (2021), arXiv:2012.00086, Theorem 1, Theorem 5, Sections 2, 5, 6 and 7.
- Fabrizio Grandoni, Christos Kalaitzis, Rico Zenklusen, "Improved Approximation for Tree Augmentation: Saving by Rewiring", STOC (2018).
- Jarosław Byrka, Fabrizio Grandoni, Afrouz Jabal Ameli, "Breaching the 2-Approximation Barrier for Connectivity Augmentation: a Reduction to Steiner Tree", STOC (2020).
