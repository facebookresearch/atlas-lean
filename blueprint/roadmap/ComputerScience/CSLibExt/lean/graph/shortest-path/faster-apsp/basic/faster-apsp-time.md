---
article_id: af_42716c07785da12b9106df74
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Matrix.fasterAPSP_time
---

# Faster APSP time

Same-run copy/fill assignments, scalar additions, and scalar products of FASTER-APSP.
The first coordinate excludes the accumulator vector updates in `matrixAccumulate`.

## Depends on

- [Faster APSP](faster-apsp.md)

## Proof depends on

- [Copy Cells](../../../../matrix/assignments/copy-cells.md)
- [Copy Cells ret](../../../../matrix/assignments/copy-cells-ret.md)
- [Copy Cells time](../../../../matrix/assignments/copy-cells-time.md)
- [Fill Cells](../../../../matrix/assignments/fill-cells.md)
- [Fill Cells time](../../../../matrix/assignments/fill-cells-time.md)
- [Matrix Accumulate](../../../../matrix/multiply/matrix-accumulate.md)
- [Matrix Accumulate time](../../../../matrix/multiply/matrix-accumulate-time.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.ShortestPath.FasterAPSP.Basic](../../../../../../../../sources/v2/CSLibExt.md)
