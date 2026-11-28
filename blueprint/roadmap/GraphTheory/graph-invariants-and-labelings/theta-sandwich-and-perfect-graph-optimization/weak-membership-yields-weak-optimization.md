# Weak membership yields weak optimization for centered convex bodies

There is an oracle-polynomial algorithm that, given a centered convex body $(K; n, R, r, a_0)$ by a weak membership oracle, solves the weak optimization problem over $K$, with running time polynomial in $n$, the encoding lengths of $R, r, a_0$, $c$ and $\log(1/\delta)$. Consequently weak membership, weak separation and weak optimization are polynomially equivalent for centered convex bodies.

## Proof sketch

Following Yudin and Nemirovski, the inner ball $B(a_0, r)$ allows a weak separation oracle to be built from weak membership queries along segments toward $a_0$, at the price of shallow instead of central cuts. Running the shallow-cut ellipsoid method on $K \cap \{x : c^\top x \ge \gamma\}$ with binary search over $\gamma$, convexity and the inner ball guarantee that the near-optimal region contains a ball of radius polynomially related to $r\delta/R$, so the volume decrease per step bounds the number of iterations polynomially.

## Depends on

- [Well-described polyhedra, centered convex bodies and the strong and weak oracle problems](well-described-polyhedra-and-oracle-problems.md)

## Proof depends on

- [Volume reduction of the ellipsoid method](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/volume-ratio-lt-exp.md)
- [The ellipsoid method finds a point](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/ellipsoid-run-finds-point.md)

## Sources

- M. Grotschel, L. Lovasz, A. Schrijver, "The ellipsoid method and its consequences in combinatorial optimization", Combinatorica 1 (1981).
- M. Grotschel, L. Lovasz, A. Schrijver, "Geometric Algorithms and Combinatorial Optimization", Springer (1988).
