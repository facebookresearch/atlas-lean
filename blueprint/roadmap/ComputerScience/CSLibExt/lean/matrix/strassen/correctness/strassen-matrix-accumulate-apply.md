---
article_id: af_72903ead39d44f2b7d62cafb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Matrix.strassenMatrixAccumulate_apply
---

# Strassen Matrix Accumulate apply

Every Strassen output entry is its saved `C` entry plus the finite row-column
product sum, with the left factor drawn from `A` and the right factor from `B`.

## Depends on

- [Basic](../strassen-matrix-accumulate.md)

## Proof depends on

- [Strassen Matrix Accumulate ret](strassen-matrix-accumulate-ret.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Matrix.Strassen.Correctness](../../../../../../../sources/v2/CSLibExt.md)
