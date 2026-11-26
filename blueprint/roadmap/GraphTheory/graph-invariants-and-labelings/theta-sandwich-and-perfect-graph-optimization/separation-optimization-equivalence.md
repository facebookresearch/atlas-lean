# Grotschel-Lovasz-Schrijver equivalence of separation and optimization

For every class $\mathcal{P}$ of well-described polyhedra, the strong separation problem over $\mathcal{P}$ is solvable in polynomial time if and only if the strong optimization problem over $\mathcal{P}$ is. More precisely, there is an oracle-polynomial algorithm that, given $(n, \varphi)$ and a strong separation oracle for $P$, solves the strong optimization problem over $P$ in time polynomial in $n$, $\varphi$ and the encoding length of $c$, and conversely there is an oracle-polynomial algorithm solving strong separation from a strong optimization oracle.

## Proof sketch

From separation to optimization: run the central-cut ellipsoid method on $P \cap \{x : c^\top x \ge \gamma\}$ with binary search over $\gamma$; the facet complexity bound gives a priori bounds on the size of vertices and on the volume of a slightly enlarged full-dimensional version of $P$, which bounds the number of iterations, and near-optimal points are rounded to exact optimal vertices by simultaneous Diophantine approximation, after first determining the affine hull when $P$ is not full-dimensional. From optimization to separation: for full-dimensional $P$ containing the origin in its interior the polar $P^\ast$ is again well-described, an optimization oracle over $P$ is a separation oracle for $P^\ast$, and applying the first direction to $P^\ast$ yields a facet of $P$ violated by the query point.

## Depends on

- [Well-described polyhedra, centered convex bodies and the strong and weak oracle problems](well-described-polyhedra-and-oracle-problems.md)

## Proof depends on

- [The ellipsoid method finds a point](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/ellipsoid-run-finds-point.md)
- [Volume reduction of the ellipsoid method](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/volume-ratio-lt-exp.md)
- [Polar of a set](../../../Analysis/convex-analysis-and-variations/polar-sets/polar-set.md)

## Sources

- M. Grotschel, L. Lovasz, A. Schrijver, "The ellipsoid method and its consequences in combinatorial optimization", Combinatorica 1 (1981).
- M. Grotschel, L. Lovasz, A. Schrijver, "Geometric Algorithms and Combinatorial Optimization", Springer (1988).
