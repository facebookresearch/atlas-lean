# Large face-move distance at prescribed dimension and facet excess

Use compact nonempty polytopes defined by finitely many linear half-space inequalities with rational coefficients in some basis of a finite-dimensional real vector space. The dimension is the affine span dimension, and facets are nonempty faces of dimension one less. A face is a convex extreme subset. A simple polytope has exactly its dimension many facets incident to each vertex. The vertices are extreme points. In the $m$-move graph two distinct vertices are adjacent if they belong to a common face of dimension at most $m$. Distances count edges, and the ordinary graph uses $m=1$.

For every real $a,b>0$, there are real $c,\delta>0$ and a natural threshold $N$ such that for all natural $d,e$ with $\min(d,e)\ge N$ there exists a simple polytope of dimension $d$ with $d+e$ facets and connected ordinary graph, having vertices at distance at least $ce\min(e^a,d^b)$ in the $\lfloor\min(d,e)^\delta\rfloor$-move graph. The quantifier is over **all** sufficiently large pairs of dimension and excess.

## Depends on

- [Simplex algorithm and the polytope model](../../../convex-geometry/linear-programming/simplex-algorithm.md)
- Bridge the finite rational half-space and finite convex-hull models; incidence of faces and distance in the graph with permitted moves.

## Proof depends on

- Build a rational polytope with the exact dimension and facet count for each pair and verify the distance under the allowed face-size floor.

## Expansion

Separate the parameter choices from the geometric construction and confirm no additional bounds on $d/e$ are imposed.

## Sources

- OpenAI Math, [`theorem_1_2`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Hirsch.lean#L153-L162) (statement and local definitions).
