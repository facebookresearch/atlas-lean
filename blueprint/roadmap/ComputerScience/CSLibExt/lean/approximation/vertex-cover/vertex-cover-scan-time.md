---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.vertexCoverScan_time
---

# Vertex Cover Scan time

CLRS `APPROX-VERTEX-COVER` over an edge list, starting from the empty cover. -/
def approxVertexCover (edges : List (V × V)) : TimeM ℕ (Finset V) :=
  vertexCoverScan ∅ edges

/-! ## Cost

## Depends on

- [Vertex Cover Scan](vertex-cover-scan.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.VertexCover](../../../../../../sources/v2/CSLibExt.md)
