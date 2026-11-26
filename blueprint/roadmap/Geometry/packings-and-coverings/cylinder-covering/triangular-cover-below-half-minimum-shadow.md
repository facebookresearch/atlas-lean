# Triangular-cylinder covers of a regular tetrahedron below half its minimum shadow

Write $H=\sqrt2$, $p(x,y,t)=(x,y,Ht)$ and $K=\{p(x,y,t):0\le t\le1,\ |x|\le1-t,\ |y|\le t\}$. If $u$ is a unit axis, let $A_K(u)$ be the Euclidean-normalized two-dimensional Hausdorff area of the orthogonal shadow of $K$ on $u^\perp$ and $A_{\min}=\inf_u A_K(u)$. A cylinder with axis $u$ and base $B\subset u^\perp$ is $B+\mathbb R u$. Its area cost is $|B|$ and its relative cost is $|B|/A_K(u)$. A triangular base is the convex hull of three affinely independent points and has finite area.

We have $A_{\min}=H$. There are $\delta,C>0$ such that for all $0<\varepsilon<\delta$, writing $n=\lceil2/\varepsilon^2\rceil$, the tetrahedron is covered by $2n$ triangular cylinders with total area $A$ satisfying

$$|A/H-(1/2-(13/6000)\varepsilon^2)|\le C\varepsilon^4,\qquad A<A_{\min}/2.$$

There also exists a finite triangular-cylinder cover with total relative cost less than $1/2$. This last witness is not required by this endpoint to be any particular family from the first clause.

## Depends on

- Tetrahedral model with perpendicular shadow measures and compact triangular cylinders.

## Proof depends on

- Minimum-shadow calculation, strip coverage, and the fourth-order area error with strictly negative quadratic term.

## Expansion

Prove the minimum-shadow formula and compare the explicit angular construction below with both cost inequalities. Preserve strictness and distinguish the two existential scopes.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TriangularCovering.lean#L65-L67) (statement and local definitions).
