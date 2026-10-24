---
article_id: af_b7e182798ef2bfa273f2e8cd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Matrix.recursiveMatrixAccumulate_time
---

# Recursive Matrix Accumulate time

The actual run performs exactly `8 ^ k` scalar multiplications and additions.
For dimension `2 ^ k` this equals its cube. Calls, indexing and allocation are uncharged.

## Depends on

- [Recursive Matrix Accumulate](recursive-matrix-accumulate.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Matrix.Recursive](../../../../../../sources/v2/CSLibExt.md)
