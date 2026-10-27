---
article_id: af_e9b841a6372fa7a9fc498c2d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted.topological_collar_neighborhood_of_smooth_manifold_with_boundary
---

# Collar Neighborhood

For `n ≥ 1` and a Hausdorff second-countable `C^∞` manifold with boundary `M` modeled on
`EuclideanHalfSpace n` via `𝓡∂ n`, there exists an open embedding collar `c : boundary M × [0, 1)
→ M` with `c (b, 0)=b`. Source: M. Hirsch, Differential Topology, GTM 33; J. Lee, Introduction to
Smooth Manifolds, 2nd ed.; Kosinski, Differential Manifolds; Lean states topological collar
`IsOpenEmbedding` corollary for `EuclideanHalfSpace` model.

Proof: Local chart collars are glued by Brown's external-collar construction, following Hatcher,
*Algebraic Topology*, Proposition 3.42, and the locally finite extension of Connelly (1971).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Manifold.CollarNeighborhood](../../../../../sources/v2/MathlibExt.md)
