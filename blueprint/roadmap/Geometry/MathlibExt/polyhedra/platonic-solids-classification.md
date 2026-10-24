---
article_id: af_97a472b1a66fbb1e2c96a2df
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.platonic_solids_classification
---

# Platonic Solids Classification

Platonic solids classification (canonical name "Platonic solids classification").

Stable source: https://en.wikipedia.org/wiki/Platonic_solid
(statement `platonic-solids-s1`).

A Platonic solid is a convex, regular polyhedron in three-dimensional Euclidean
space: its faces are congruent regular polygons (all edges congruent and all
face angles congruent), and the same number of faces meet at each vertex. The
ambient `E^3` is `EuclideanSpace ℝ (Fin 3)`. Convexity follows from the `body`
hypothesis `body = convexHull ℝ (Set.range verts)`, which pins the solid to the
polyhedron spanned by the vertices (and is also assumed as `Convex ℝ body`); the
convex-position hypothesis (each vertex lies outside the convex hull of the
others) makes every listed vertex an extreme point. Regularity and congruence are
interpreted Euclidean conditions over the vertex/face data, not uninterpreted
predicate variables: uniform edge lengths via `dist ... = l`, uniform
face-angle congruence via uniform vertex-angle diagonals
`dist ... = angleDiag` (with uniform side length `l`, equal diagonals give
equal Euclidean vertex angles by SSS; for `p = 3` this forces `angleDiag = l`),
and the same number `q` of faces meeting at every vertex via `Set.ncard`.
Each face has distinct vertices (`Function.Injective`), every face edge is
realized by a graph edge and every graph edge is a face edge (tying edge and
face data to each other), and each edge hull and each filled face
(`convexHull` of its vertices) lies in `body` (tying the combinatorial data to
the polyhedral boundary). Faces are planar: the span of pairwise vertex
differences of each face has `Module.finrank` at most two. Edges are pairwise
duplicate-free (equal unordered endpoint pairs force equal edge indices) and
faces are pairwise duplicate-free (equal vertex ranges force equal face
indices). All features are pinned to the boundary: every vertex lies in
`frontier body`, and every edge hull and filled face lies in `frontier body`.
The incidence relations `2 * E = p * F` and `2 * E = q * V` record face
regularity/congruence and the equal face count, and the Euler characteristic
`(V : ℤ) - (E : ℤ) + (F : ℤ) = 2` is assumed as the convex-polyhedron relation
in `E^3`. Non-degeneracy is `3 ≤ p`, `3 ≤ q`, `0 < V`, `0 < E`, `0 < F`,
`0 < l`, `0 < angleDiag`.
Repair conditions: (1) full-dimensionality (`Module.finrank` of the span of
pairwise vertex differences equals 3); (2) facet/supporting-plane condition
(each face lies in a supporting hyperplane `inner n x ≤ c` of `body`, with face
vertices satisfying `inner n ... = c` for some nonzero normal `n`);
(3) boundary coverage (every point of `frontier body` lies in some filled
face); (4) exact two-face edge incidence (`Set.ncard` of faces containing each
edge equals 2); (5) simple convex face ordering (each face vertex lies outside
the convex hull of the other vertices of the same face, with cyclic adjacency
`j.val = (i.val + 1) % p` plus pairwise `Disjoint`ness of cyclic-edge segments with
disjoint endpoints (simple-polygon condition ruling out star/bow-tie orderings, so the
SSS diagonal encoding is sound)).
The conclusion both enumerates exactly the five solutions as `(p, q, V, E, F)`:
tetrahedron `(3, 3, 4, 6, 4)`, cube `(4, 3, 8, 12, 6)`, octahedron
`(3, 4, 6, 12, 8)`, dodecahedron `(5, 3, 20, 30, 12)`, icosahedron
`(3, 5, 12, 30, 20)`, and, unconditionally, asserts existence of a realization
of each of the five named solids with the same interpreted regularity,
simple-polygon edge-disjointness, and counting relations (classification up to the
`(p, q, V, E, F)` count tuple, not up to Euclidean congruence via an explicit isometry),
planarity, convex-position, edge-face incidence, duplicate-freeness, boundary
pinning, full-dimensionality, supporting-plane, boundary coverage, two-face
incidence, face convex-position, and counting relations.

Proof: Euler's formula and the two incidence-count equations give `1 / p + 1 / q > 1 / 2`,
which bounds `p` and `q` and leaves the five listed tuples. Explicit coordinates verify a
realization of each tuple.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Polyhedra.PlatonicSolidsClassification](../../../../sources/v2/MathlibExt.md)
