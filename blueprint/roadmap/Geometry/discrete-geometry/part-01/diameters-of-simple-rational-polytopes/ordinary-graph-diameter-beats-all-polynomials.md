# Ordinary diameters of simple rational polytopes exceed every polynomial

Use compact nonempty polytopes defined by finitely many linear half-space inequalities with rational coefficients in some basis of a finite-dimensional real vector space. The dimension is the affine span dimension, and facets are nonempty faces of dimension one less. A face is a convex extreme subset. A simple polytope has exactly its dimension many facets incident to each vertex. The vertices are extreme points. In the $m$-move graph two distinct vertices are adjacent if they belong to a common face of dimension at most $m$. Distances count edges, and the ordinary graph uses $m=1$.

There is a family $P_n$ such that eventually it is simple, its ordinary graph is connected and it has exactly $n$ facets. For every $\varepsilon>0$, its dimension is eventually at most $n^\varepsilon$. For every real $q$ its ordinary graph diameter is eventually at least $n^q$, equivalently for every real polynomial $p$ the diameter is eventually strictly larger than $p(n)$. Both bounds use the same single family within each quantified statement.

## Depends on

- [Simplex algorithm and the polytope model](../../../convex-geometry/linear-programming/simplex-algorithm.md)
- Bridge the finite rational half-space and finite convex-hull models; incidence of faces and distance in the graph with permitted moves.

## Proof depends on

- [Face-move distance family](superpolynomial-distance-with-face-moves.md)
- Pass from face moves to ordinary graph distance with the constant choice $m(n)=1$, and compare positive real powers and polynomials.

## Expansion

Prove the two growth formulations equivalent by dominating each fixed polynomial by a strictly larger power and choosing an integer exponent above a given real exponent for the converse. Do not replace eventual domination by an infinite subsequence.

## Sources

- OpenAI Math, [`superpolynomial_graph_diameter`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Hirsch.lean#L132-L139) (statement and local definitions).
- OpenAI Math, [`graph_diameter_beats_polynomials`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Hirsch.lean#L140-L147).
