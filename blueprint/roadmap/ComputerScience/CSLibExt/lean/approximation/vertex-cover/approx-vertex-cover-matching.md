---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.approxVertexCover_matching
---

# Approx Vertex Cover matching

The edges `APPROX-VERTEX-COVER` takes form a maximal matching `A` of the listed edges:
they are listed edges, pairwise vertex-disjoint, every listed edge shares an endpoint with one of
them, the returned cover is exactly their endpoints, and it has `2 * A.length` vertices.

## Depends on

- [Vertex Disjoint](vertex-disjoint.md)
- [Approx Vertex Cover](approx-vertex-cover.md)

## Proof depends on

- [Approx Vertex Cover covers](approx-vertex-cover-covers.md)
- [Exists matching vertex Cover Scan](exists-matching-vertex-cover-scan.md)
- [Vertex Cover Scan](vertex-cover-scan.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.VertexCover](../../../../../../sources/v2/CSLibExt.md)
