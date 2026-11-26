# Superpolynomial distances with subpolynomially large face moves

Use compact nonempty polytopes defined by finitely many linear half-space inequalities with rational coefficients in some basis of a finite-dimensional real vector space. The dimension is the affine span dimension, and facets are nonempty faces of dimension one less. A face is a convex extreme subset. A simple polytope has exactly its dimension many facets incident to each vertex. The vertices are extreme points. In the $m$-move graph two distinct vertices are adjacent if they belong to a common face of dimension at most $m$. Distances count edges, and the ordinary graph uses $m=1$.

For every integer sequence $m(n)>0$ with $m(n)\le n^\varepsilon$ eventually for every $\varepsilon>0$, there is a family $P_n$ with a linear objective and specified minimizing and maximizing vertices of distinct objective values for every $n$. Eventually $P_n$ is simple with connected ordinary graph and exactly $n$ facets, and its dimension is subpolynomial in the same sense. The $m(n)$-move distance from the maximizing to the minimizing vertex is eventually at least $n^q$ for every real $q$; the $m(n)$-move graph diameter also has this property. For every $0<\alpha<1$ and real $q$, eventually **all** vertex pairs whose absolute objective difference, divided by the full objective range, is at least $n^{-\alpha}$ have distance at least $n^q$.

## Depends on

- [Simplex algorithm and the polytope model](../../../convex-geometry/linear-programming/simplex-algorithm.md)
- Bridge the finite rational half-space and finite convex-hull models; incidence of faces and distance in the graph with permitted moves.

## Proof depends on

- Analyze face moves in the constructed family and lower-bound the distance uniformly for all pairs with the normalized objective gap.

## Expansion

The two formulations select the same kind of family and share the objective-gap clause. Endpoints have normalized gap one, so that clause implies the extremal distance bound; on the eventually connected graph, diameter is at least this distance. Thus the endpoint and diameter variants share one page.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Hirsch.lean#L108-L120) (statement and local definitions).
- OpenAI Math, [`theorem_1_1`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Hirsch.lean#L121-L131).
