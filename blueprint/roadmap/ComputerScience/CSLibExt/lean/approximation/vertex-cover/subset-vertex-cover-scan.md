---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.subset_vertexCoverScan
---

# Subset vertex Cover Scan

One unit per listed edge. -/
@[simp]
theorem approxVertexCover_time (edges : List (V × V)) :
    (approxVertexCover edges).time = edges.length :=
  vertexCoverScan_time ∅ edges

/-! ## The result is a vertex cover

## Depends on

- [Vertex Cover Scan](vertex-cover-scan.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.VertexCover](../../../../../../sources/v2/CSLibExt.md)
