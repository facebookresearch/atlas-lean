---
article_id: af_ac5043b6f696b0c2df1a6de1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: LipschitzImageCubeCount.exists_cubeCount_le_const_mul_pow
---

# Exists cube Count le const mul pow

Real `O(t ^ d)` consequence (source lines 283–311): with
`M = 2 * ⌈K * √d⌉₊ + 3`, the constant `C = 2 ^ d * M ^ n` depends on `f`
(through `K`), `n`, and `d`, but not on `t`. Uses `⌈t⌉₊ ≤ 2 * t` for `t ≥ 1`.

## Depends on

- [Integer Cube Set](integer-cube-set.md)
- [Unit Cube](../../../Topology/MathlibExt/metric-space/lipschitz-parametrizable/unit-cube.md)

## Proof depends on

- [Card integer Cube Set le](card-integer-cube-set-le.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.LipschitzImageCubeCount](../../../../sources/v2/MathlibExt.md)
