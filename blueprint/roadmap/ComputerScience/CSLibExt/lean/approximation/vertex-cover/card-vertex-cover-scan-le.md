---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.card_vertexCoverScan_le
---

# Card vertex Cover Scan le

The counting invariant: every vertex cover `S` of `G` contains at least half of the vertices
the scan has chosen, because each taken edge adds two new vertices, at least one of them in `S`.

## Depends on

- [Vertex Cover Scan](vertex-cover-scan.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.VertexCover](../../../../../../sources/v2/CSLibExt.md)
