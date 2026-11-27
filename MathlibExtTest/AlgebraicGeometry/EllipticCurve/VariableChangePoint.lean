/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePoint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint

open WeierstrassCurve

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The test curve `y² = x³ + x` over `ZMod 5`. -/
private def curve : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 0⟩

private instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  decide

/-- Translation by one in the affine `x` coordinate. -/
private def change : VariableChange (ZMod 5) :=
  ⟨1, 1, 0, 0⟩

set_option maxHeartbeats 400000 in
-- Elaborating both concrete point types needs more than the default deterministic budget.
/-- A nontrivial translation preserves the number of points of a concrete curve over `ZMod 5`. -/
example : Nat.card ((change • curve).toAffine.Point) = Nat.card curve.toAffine.Point :=
  VariableChange.natCard_point_eq change curve

/-- `exactSource` consumer: the source theorem, that the inverse variable change preserves
addition of points, is `map_add` of the inverse of the additive equivalence. -/
example {K : Type*} [Field K] [DecidableEq K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K)
    (P Q : W.toAffine.Point) :
    (WeierstrassCurve.Affine.Point.variableChangeAddEquiv C W).symm (P + Q) =
      (WeierstrassCurve.Affine.Point.variableChangeAddEquiv C W).symm P +
        (WeierstrassCurve.Affine.Point.variableChangeAddEquiv C W).symm Q :=
  map_add _ P Q

/-- The inverse variable change fixes the point at infinity, so the hypothesis
that a point is affine is essential for coordinate formulae: at infinity
there are no coordinates to transform. -/
example {K : Type*} [Field K] [DecidableEq K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    (WeierstrassCurve.Affine.Point.variableChangeAddEquiv C W).symm (0 : W.toAffine.Point) = 0 :=
  map_zero _

/-! ### Concrete coordinates and sums over `ZMod 5`

`change` has `u = 1` and `s = t = 0`, so it cannot tell the `u`, `s` and `t` terms of the
coordinate formulas apart; `change₂` uses nonzero values for all four parameters. -/

/-- The variable change `(u, r, s, t) = (2, 1, 3, 4)` over `ZMod 5`. -/
private def change₂ : VariableChange (ZMod 5) :=
  ⟨⟨2, 3, by decide, by decide⟩, 1, 3, 4⟩

/-- The coordinate map is `(x, y) ↦ (u² x + r, u³ y + u² s x + t)`: it sends `(1, 3)` to
`(0, 0)` and `(4, 1)` to `(2, 0)`. -/
example : VariableChange.mapAffineCoordinates change₂ (1, 3) = (0, 0) ∧
    VariableChange.mapAffineCoordinates change₂ (4, 1) = (2, 0) := by
  decide

/-- The coordinate map of the inverse change is `(x, y) ↦ (u⁻² (x - r), u⁻³ (y - t - s (x - r)))`:
it sends `(0, 0)` to `(1, 3)` and `(2, 0)` to `(4, 1)`. -/
example : VariableChange.mapAffineCoordinates change₂⁻¹ (0, 0) = (1, 3) ∧
    VariableChange.mapAffineCoordinates change₂⁻¹ (2, 0) = (4, 1) := by
  decide

/-- The variable change `(u, r, s, t) = (2, 1, 3, 4)` over `ℚ`. Over `ZMod 5` every unit
satisfies `u ^ 4 = 1`, so `u²` and `u⁻²` agree there; over `ℚ` they differ. -/
private def changeℚ : VariableChange ℚ :=
  ⟨⟨2, 2⁻¹, by norm_num, by norm_num⟩, 1, 3, 4⟩

/-- Over `ℚ`, the coordinate maps of `changeℚ` and its inverse send `(2, 1)` to `(9, 36)` and
back. -/
example : VariableChange.mapAffineCoordinates changeℚ (2, 1) = (9, 36) ∧
    VariableChange.mapAffineCoordinates changeℚ⁻¹ (9, 36) = (2, 1) := by
  norm_num [changeℚ, VariableChange.mapAffineCoordinates, VariableChange.inv_def]

/-- The point `(0, 0)` of `curve`. -/
private def p₀₀ : curve.toAffine.Point :=
  .some 0 0 (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide)

/-- The point `(2, 0)` of `curve`. -/
private def p₂₀ : curve.toAffine.Point :=
  .some 2 0 (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide)

/-- The point `(3, 0)` of `curve`. -/
private def p₃₀ : curve.toAffine.Point :=
  .some 3 0 (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide)

/-- The point `(1, 3)` of the transformed curve `change₂ • curve`. -/
private def q₁₃ : (change₂ • curve).toAffine.Point :=
  .some 1 3 (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide)

/-- The point `(4, 1)` of the transformed curve `change₂ • curve`. -/
private def q₄₁ : (change₂ • curve).toAffine.Point :=
  .some 4 1 (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide)

/-- The point `(3, 0)` of the transformed curve `change₂ • curve`. -/
private def q₃₀ : (change₂ • curve).toAffine.Point :=
  .some 3 0 (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide)

/-- On `curve`, the chord through `(0, 0)` and `(2, 0)` has slope `0` and meets the curve again
at `(3, 0)`, so `(0, 0) + (2, 0) = (3, 0)`. -/
private theorem p₀₀_add_p₂₀ : p₀₀ + p₂₀ = p₃₀ := by
  have hL : curve.toAffine.slope 0 2 0 0 = 0 := by
    rw [Affine.slope_of_X_ne (by decide : (0 : ZMod 5) ≠ 2), sub_self, zero_div]
  rw [p₀₀, p₂₀, p₃₀,
    Affine.Point.add_some (by decide : ¬((0 : ZMod 5) = 2 ∧
      (0 : ZMod 5) = curve.toAffine.negY 2 0)),
    Affine.Point.some.injEq, hL]
  decide

/-- On `change₂ • curve`, the chord through `(1, 3)` and `(4, 1)` has slope `1`, and
`(1, 3) + (4, 1) = (3, 0)`. -/
private theorem q₁₃_add_q₄₁ : q₁₃ + q₄₁ = q₃₀ := by
  have hL : (change₂ • curve).toAffine.slope 1 4 3 1 = 1 := by
    rw [Affine.slope_of_X_ne (by decide : (1 : ZMod 5) ≠ 4),
      div_eq_iff (by decide : (1 - 4 : ZMod 5) ≠ 0)]
    decide
  rw [q₁₃, q₄₁, q₃₀,
    Affine.Point.add_some (by decide : ¬((1 : ZMod 5) = 4 ∧
      (3 : ZMod 5) = (change₂ • curve).toAffine.negY 4 1)),
    Affine.Point.some.injEq, hL]
  decide

/-- The additive equivalence sends the point `(1, 3)` of the transformed curve to `(0, 0)`. -/
example : Affine.Point.variableChangeAddEquiv change₂ curve q₁₃ = p₀₀ := by
  simp only [q₁₃, p₀₀, Affine.Point.variableChangeAddEquiv_some, Affine.Point.some.injEq]
  decide

/-- The inverse of the additive equivalence sends the point `(2, 0)` of `curve` to `(4, 1)`. -/
example : (Affine.Point.variableChangeAddEquiv change₂ curve).symm p₂₀ = q₄₁ := by
  simp only [p₂₀, q₄₁, Affine.Point.variableChangeAddEquiv_symm_some, Affine.Point.some.injEq]
  decide

/-- The additive equivalence carries the sum `(1, 3) + (4, 1)` on the transformed curve to the sum
`(0, 0) + (2, 0)` on `curve`; both sums are computed from the chord formulas above, not from
additivity of the equivalence. -/
example : Affine.Point.variableChangeAddEquiv change₂ curve (q₁₃ + q₄₁) = p₀₀ + p₂₀ := by
  rw [q₁₃_add_q₄₁, p₀₀_add_p₂₀]
  simp only [q₃₀, p₃₀, Affine.Point.variableChangeAddEquiv_some, Affine.Point.some.injEq]
  decide

/-- On the elliptic `curve`, the point bijection `VariableChange.pointEquiv` is the underlying
equivalence of the additive equivalence, so it also sends `(1, 3)` to `(0, 0)`. -/
example : VariableChange.pointEquiv change₂ curve q₁₃ = p₀₀ := by
  rw [← Affine.Point.variableChangeAddEquiv_toEquiv]
  simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, q₁₃, p₀₀,
    Affine.Point.variableChangeAddEquiv_some, Affine.Point.some.injEq]
  decide

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.VariableChangePoint
