# Face correspondence under triangle expansion

Let $G$ be a finite loopless multigraph with a perfect matching and a vertex $v$ of degree exactly three, counting labelled edges. Label the three incident edges $e_i$ by $i\in\mathbb Z/3$. Replace $v$ by tips $v_i$, attaching $e_i$ at $v_i$ and placing a new edge $g_i$ between $v_{i+1}$ and $v_{i+2}$. If $P_G,P_H$ are the two perfect-matching polytopes, let $Q$ be the part of $P_H$ where the sum on the cut of the triangle is one. Define $f$ on all old-edge vectors by preserving old coordinates and setting $f(x)_{g_i}=x_{e_i}$. There is such a labelling for which $f(P_G)=Q$, $Q$ is convex and extreme in $P_H$, restriction to old coordinates is a left inverse on all vectors and a right inverse on $Q$, $f$ sends the all-$1/3$ vector to the all-$1/3$ vector, and for every $x\in P_G$ the minimal face of $P_H$ containing $f(x)$ is the image of the minimal face of $P_G$ containing $x$. Here a minimal face is the intersection of the convex extreme subsets of the polytope containing the point.

## Depends on

- [Edges incident to a vertex in an endpoint-map multigraph](../../graph-families-and-operations/finite-multigraphs/incident.md), with distinct endpoints for each edge. The perfect-matching polytope is the convex hull of the indicators of labelled edge subsets that have exactly one incident edge per vertex.
- [Cut of a vertex set](../../graph-families-and-operations/finite-multigraphs/cut.md); its mass is the sum of its edge coordinates.
- Multigraph triangle replacement and convex extreme subsets.

## Proof outline

Prove these prerequisites in that order; separate the coordinate restriction identities from minimal-face transport. The all-$1/3$ assertion is conditional on input coordinates, not membership in the polytope.

- Perfect-matching bijection for the active cut, cut mass at least one for every matching, and transport of minimal faces through this face.

## Sources

- [Comparator statement: `OAI.TriangleFace198.triangle_expansion_face`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TriangleFace.lean#L169-L186)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/113.md)
