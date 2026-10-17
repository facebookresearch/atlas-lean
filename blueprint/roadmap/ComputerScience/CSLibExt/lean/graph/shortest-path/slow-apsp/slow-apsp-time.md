---
article_id: af_399b119778d40f1eec92c614
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Matrix.slowAPSP_time
---

# Slow APSP time

Exact copy/fill assignment, scalar-addition, and scalar-minimum counts.
The first coordinate excludes the accumulator vector updates in `matrixAccumulate`.

## Depends on

- [Slow APSP](slow-apsp.md)

## Proof depends on

- [Copy Cells](../../../matrix/assignments/copy-cells.md)
- [Copy Cells ret](../../../matrix/assignments/copy-cells-ret.md)
- [Copy Cells time](../../../matrix/assignments/copy-cells-time.md)
- [Fill Cells](../../../matrix/assignments/fill-cells.md)
- [Fill Cells ret](../../../matrix/assignments/fill-cells-ret.md)
- [Fill Cells time](../../../matrix/assignments/fill-cells-time.md)
- [Matrix Accumulate](../../../matrix/multiply/matrix-accumulate.md)
- [Matrix Accumulate time](../../../matrix/multiply/matrix-accumulate-time.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.SlowAPSP](../../../../../../../sources/v2/CSLibExt.md)
