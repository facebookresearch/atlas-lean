# No uniform polynomial Hirsch bound for simple rational polytopes

Use compact nonempty polytopes defined by finitely many linear half-space inequalities with rational coefficients in some basis of a finite-dimensional real vector space. The dimension is the affine span dimension, and facets are nonempty faces of dimension one less. A face is a convex extreme subset. A simple polytope has exactly its dimension many facets incident to each vertex. The vertices are extreme points. In the $m$-move graph two distinct vertices are adjacent if they belong to a common face of dimension at most $m$. Distances count edges, and the ordinary graph uses $m=1$.

There are no natural constants $C,e$ such that, for every simple rational polytope with connected ordinary graph, every vertex-pair distance is at most $C(f+1)^e$, where $f$ is its number of facets. This is the negation of a uniform bound on all such polytopes, not a claim about one fixed dimension.

## Depends on

- [Simplex algorithm and the polytope model](../../../convex-geometry/linear-programming/simplex-algorithm.md)
- Bridge the finite rational half-space and finite convex-hull models; incidence of faces and distance in the graph with permitted moves.

## Proof depends on

- [Eventual superpolynomial graph diameters](ordinary-graph-diameter-beats-all-polynomials.md)
- Use a family whose ordinary diameters eventually exceed the candidate polynomial.

## Expansion

Show that on the connected finite vertex graph the diameter is attained by a pair, then use the prescribed candidate polynomial with $f=n$.

## Sources

- OpenAI Math, [`not_polynomialHirsch`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Hirsch.lean#L148-L152) (statement and local definitions).
