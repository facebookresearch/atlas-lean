---
article_id: af_eb37bec88de7cab104c0e2c9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.routh
---

# Routh's theorem

**Routh's theorem** (canonical name "Routh's theorem", statement `routh-s1`).

Triangle `ABC` with cevians from each vertex dividing the opposite side in
ratios `x`, `y`, `z`: `D` on `BC` with `DC / DB = x`, `E` on `CA` with
`EA / EC = y`, `F` on `AB` with `FB / FA = z`. The cevians `AD`, `BE`, `CF`
meet pairwise in the inner triangle `PQR`. Its area is
`(x * y * z - 1) ^ 2 / ((x * y + y + 1) * (y * z + z + 1) * (z * x + x + 1))`
times the area of `ABC` (areas via `MeasureTheory.volume` of `convexHull`s).
Nondegeneracy: `ABC` has nonzero area, the ratios are positive, and
`x * y * z ≠ 1`.

Stable source: https://en.wikipedia.org/wiki/Routh%27s_theorem
Proves `Wanted` entry `routh`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Routh](../../../../../sources/v2/MathlibExt.md)
