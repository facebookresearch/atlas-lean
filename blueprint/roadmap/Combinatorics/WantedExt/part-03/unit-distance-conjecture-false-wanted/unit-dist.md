---
article_id: af_daceb1b2ceb2e0be024def29
declaration: abbrev
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.UnitDistanceConjectureFalseWanted.Combinatorics.unitDist
---

# Unit Dist

For a finite planar set `P ⊆ ℝ²`, `unitDist P` is the number of
unordered pairs `{x, y} ⊆ P` at Euclidean distance exactly `1`.

Points are modelled as `EuclideanSpace ℝ (Fin 2)` rather than `ℝ × ℝ`
so that `dist x y = √((x₀ - y₀)² + (x₁ - y₁)²)`; the product space
`ℝ × ℝ` carries the sup-norm and would give the wrong notion of
unit-distance pair.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Unit Dist Num](../../../../Geometry/MathlibExt/metric/unit-dist-num.md)

## Sources

- [WantedExt, WantedExt.Combinatorics.UnitDistanceConjectureFalseWanted](../../../../../sources/v2/WantedExt.md)
