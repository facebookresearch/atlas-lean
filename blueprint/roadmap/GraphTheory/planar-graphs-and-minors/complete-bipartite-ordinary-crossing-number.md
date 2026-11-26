# Ordinary crossing formula for complete bipartite graphs

For positive integers $m,n$, draw $K_{m,n}$ in $\mathbb R^2$ with distinct vertex positions and simple continuous unit-interval paths for edges, whose interiors avoid every vertex. Distinct edge interiors meet at finitely many points altogether, never three at once, and each intersection of two interiors is proper: an open local chart sends the crossing to the origin and the two local arcs to the horizontal and vertical coordinate axes in its target. Count distinct crossing points (not pairs of edges). There exists such a drawing having exactly

$$
\lfloor m/2\rfloor\lfloor(m-1)/2\rfloor\lfloor n/2\rfloor\lfloor(n-1)/2\rfloor
$$

crossings, and every such drawing has at least this many.

## Depends on

- Admissible continuous graph drawing, local straightening of proper intersections, and finite spatial crossing count.

## Proof outline

Build the attaining drawing with no triple intersections, and state the lower bound independently; it must allow adjacent edges to intersect and count repeated intersections of a given pair separately. Reconcile the curve model with any canonical drawing definitions before linking.

- Matching attaining drawing and general lower bound in the continuous ordinary-crossing model.

## Sources

- [Comparator statement: `OAI.Zarankiewicz.mainTarget_proof`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BipartiteCrossing.lean#L60-L62)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/165.md)
