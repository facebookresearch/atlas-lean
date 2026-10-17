---
article_id: af_baa42599f3401b6606dce078
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Matrix.slowAPSP
---

# Slow APSP

Execute CLRS SLOW-APSP with explicit copy/fill assignment charges.
Accumulator vector updates in `matrixAccumulate` are outside these assignment charges.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Copy Cells](../../../matrix/assignments/copy-cells.md)
- [Fill Cells](../../../matrix/assignments/fill-cells.md)
- [Matrix Accumulate](../../../matrix/multiply/matrix-accumulate.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.SlowAPSP](../../../../../../../sources/v2/CSLibExt.md)
