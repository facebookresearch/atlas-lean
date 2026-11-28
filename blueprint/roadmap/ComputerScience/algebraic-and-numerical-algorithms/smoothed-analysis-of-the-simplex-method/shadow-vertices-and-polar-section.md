# Shadow vertices are bounded by edges of the polar section

Let $a_1, \dots, a_n \in \mathbb{R}^d$, let $P = \{x : \langle a_i, x \rangle \le 1 \text{ for all } i\}$, let $Q = \mathrm{conv}(a_1, \dots, a_n)$ and let $W$ be a $2$-dimensional linear subspace. Suppose that $P$ is nondegenerate and that its shadow on $W$ is nondegenerate, in the sense of the shadow vertex rule. Then the number of vertices of the shadow $\pi_W(P)$ is at most the number of edges of the polygon $Q \cap W$.

## Proof sketch

A vertex of $\pi_W(P)$ is the image of a vertex $x$ of $P$ that maximizes some objective $\theta \in W$ over $P$; at such $x$ the tight constraints $I$ satisfy $\theta \in \mathrm{cone}(a_i : i \in I)$ by linear programming duality. Rescaling, the ray through $\theta$ leaves $Q \cap W$ through the face $\mathrm{conv}(a_i : i \in I) \cap W$, which, because the shadow is nondegenerate, is an edge of the polygon $Q \cap W$ (a degenerate shadow can make several tight sets meet $W$ at one point, or make a vertex of $P$ project into the interior of a shadow edge), and distinct vertices of the shadow give distinct tight sets and hence distinct edges. This is Borgwardt's polarity argument, the starting point of all shadow bounds.

## Depends on

- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Proof depends on

- [Polar of a set](../../../Analysis/convex-analysis-and-variations/polar-sets/polar-set.md)
- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- K. H. Borgwardt, "The Simplex Method: A Probabilistic Analysis", Springer (1987).
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667, Section 2 (Lemma 11).
