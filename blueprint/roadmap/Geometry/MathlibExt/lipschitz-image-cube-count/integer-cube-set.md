---
article_id: af_b4745b656fd3595776f269db
declaration: def
origin: cited
statement: formalized
lean: LipschitzImageCubeCount.integerCubeSet
---

# Integer Cube Set

The set of integer unit-cube indices meeting the dilate `t • f (unitCube d)`.
A vector `v : Fin n → ℤ` is included when some cube point `y` has `t * f y` in
the half-open cube `[vᵢ, vᵢ + 1)` in every coordinate.

## Depends on

- [Unit Cube](../../../Topology/MathlibExt/metric-space/lipschitz-parametrizable/unit-cube.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.LipschitzImageCubeCount](../../../../sources/v2/MathlibExt.md)
