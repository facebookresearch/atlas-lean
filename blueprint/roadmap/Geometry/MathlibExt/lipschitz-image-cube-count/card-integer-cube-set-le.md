---
article_id: af_6ae0d8957942bf7ca74facfe
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: LipschitzImageCubeCount.card_integerCubeSet_le
---

# Card integer Cube Set le

Explicit finite-grid cardinality estimate (source lines 114–222).
Put `T = ⌈t⌉₊` and partition the cube into `T ^ d` cells with lower-corner
representatives; Lipschitz control bounds every floor-coordinate offset from
the representative by `L = ⌈K * √d⌉₊`, and each met integer cube is encoded
injectively by its cell and an offset in `Fin (2 * L + 3) ^ n`.

## Depends on

- [Integer Cube Set](integer-cube-set.md)
- [Unit Cube](../../../Topology/MathlibExt/metric-space/lipschitz-parametrizable/unit-cube.md)

## Proof depends on

- [Abs floor sub le ceil](abs-floor-sub-le-ceil.md)
- [Mem integer Cube Set iff](mem-integer-cube-set-iff.md)
- [Scaled coord abs le](scaled-coord-abs-le.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.LipschitzImageCubeCount](../../../../sources/v2/MathlibExt.md)
