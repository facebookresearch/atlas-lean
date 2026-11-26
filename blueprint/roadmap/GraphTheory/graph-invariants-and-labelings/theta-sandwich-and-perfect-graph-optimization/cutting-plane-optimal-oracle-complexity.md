# Cutting planes with O(n log kappa) separation queries and O(n^2) work per query

Let $K \subseteq \mathbb{R}^n$ be convex and contained in a box of radius $R$, given by a separation oracle with cost $\mathrm{SO}$ per call, let $\varepsilon > 0$ and $\kappa = nR/\varepsilon$. There is a randomized algorithm that either finds a point of $K$ or proves that $K$ contains no ball of radius $\varepsilon$, using $O(n \log \kappa)$ oracle calls and $O(n^2)$ additional arithmetic operations per call, for total time

$$
O\!\left(\mathrm{SO} \cdot n \log \kappa + n^3 \log \kappa\right) .
$$

This improves Vaidya's $O(\mathrm{SO} \cdot n \log \kappa + n^{\omega + 1} \log \kappa)$ and Lee-Sidford-Wong's $O(\mathrm{SO} \cdot n \log \kappa + n^3 \log^{O(1)} \kappa)$, whereas the central-cut ellipsoid method needs $O(n^2 \log \kappa)$ oracle calls.

## Proof sketch

The method follows Vaidya's volumetric center scheme and Lee-Sidford-Wong's hybrid center, which add or remove one cutting plane per step while a potential function combining volume and leverage scores decreases by a constant, so $O(n \log \kappa)$ steps suffice. The bottleneck is maintaining approximate leverage scores of the current constraint matrix; a multi-layered data structure combining random projection, batched low-rank updates, inverse maintenance, polynomial interpolation and fast rectangular matrix multiplication keeps this at $O(n^2)$ amortized time per step.

## Depends on

- [Well-described polyhedra, centered convex bodies and the strong and weak oracle problems](well-described-polyhedra-and-oracle-problems.md)

## Proof depends on

- [Volume reduction of the ellipsoid method](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/volume-ratio-lt-exp.md)

## Sources

- H. Jiang, Y. T. Lee, Z. Song, S. C. Wong, "An Improved Cutting Plane Method for Convex Optimization, Convex-Concave Games and its Applications", STOC (2020), arXiv:2004.04250.
- Y. T. Lee, A. Sidford, S. C. Wong, "A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization", FOCS (2015), arXiv:1508.04874.
