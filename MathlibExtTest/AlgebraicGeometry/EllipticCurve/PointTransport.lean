/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.PointTransport
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointTransport

open WeierstrassCurve

universe u v

variable {F : Type u} {k : Type v} [Field F] [Field k] [DecidableEq F]
  [DecidableEq k] (f : F →+* k) {W₀ : WeierstrassCurve F}

/-- Unfolding consumer: `mapPoint` on a `some` point applies `f` to
both coordinates. -/
example {x y : F} (h : W₀.toAffine.Nonsingular x y) :
    mapPoint f (.some x y h) =
      .some (f x) (f y)
        ((W₀.toAffine.map_nonsingular f.injective x y).mpr h) :=
  mapPoint_some f h

/-- The induced group homomorphism preserves addition, scalar
multiplication, and additive order, with all hypotheses instantiated. -/
example (P Q : W₀.toAffine.Point) (n : ℕ) :
    mapPoint f (P + Q) = mapPoint f P + mapPoint f Q ∧
      mapPoint f (n • P) = n • mapPoint f P ∧
        addOrderOf (mapPoint f P) = addOrderOf P :=
  ⟨mapPoint_add f P Q, mapPoint_nsmul f n P, addOrderOf_mapPoint f P⟩

/-- The additive equivalence from an equality of curves is the
identity on the diagonal. -/
example (W : WeierstrassCurve F) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ :=
  pointAddEquivOfEq_refl W

/-- Nonsingularity transports along the affine coordinate map of a
variable change. -/
example {K : Type u} [Field K] (C : VariableChange K)
    (W : WeierstrassCurve K) (x y : K) :
    (C • W).toAffine.Nonsingular x y ↔
      W.toAffine.Nonsingular (VariableChange.mapAffineCoordinates C (x, y)).1
        (VariableChange.mapAffineCoordinates C (x, y)).2 :=
  VariableChange.nonsingular_mapAffineCoordinates_iff C W (x, y)

/-- Application consumer, with no decidability assumption: the
equivalence sends an affine point `(x, y)` of `C • W` to
`(u²x + r, u³y + u²sx + t)`. -/
example {K : Type u} [Field K] (C : VariableChange K)
    (W : WeierstrassCurve K) {x y : K} (h : (C • W).toAffine.Nonsingular x y) :
    Affine.Point.variableChangeEquiv C W (.some x y h) =
      .some ((C.u : K) ^ 2 * x + C.r)
        ((C.u : K) ^ 3 * y + (C.u : K) ^ 2 * C.s * x + C.t)
        ((VariableChange.nonsingular_mapAffineCoordinates_iff C W (x, y)).mp h) :=
  Affine.Point.variableChangeEquiv_some h

/-- On an elliptic curve the equivalence is the existing elliptic-curve
point equivalence `VariableChange.pointEquiv`. -/
example {K : Type u} [Field K] (C : VariableChange K)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Affine.Point.variableChangeEquiv C W = VariableChange.pointEquiv C W := by
  ext P
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Translation by one in the affine `x` coordinate. -/
private def change5 : VariableChange (ZMod 5) :=
  ⟨1, 1, 0, 0⟩

/-- The test curve `y² = x³ + x` over `ZMod 5`. -/
private def curve5 : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 0⟩

/-- The point `(1, 0)` of the translated curve. -/
private theorem nonsingular_change5_curve5 :
    (change5 • curve5).toAffine.Nonsingular 1 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  decide

/-- The point `(2, 0)` of `y² = x³ + x`. -/
private theorem nonsingular_curve5 : curve5.toAffine.Nonsingular 2 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  decide

/-- A nontrivial instance of the variable-change point equivalence:
translation by `1` in the `x`-coordinate on `y² = x³ + x` over
`ZMod 5` fixes the zero point and sends the point `(1, 0)` of the
translated curve to `(2, 0)`. -/
example :
    Affine.Point.variableChangeEquiv change5 curve5 0 = 0 ∧
      Affine.Point.variableChangeEquiv change5 curve5
          (.some 1 0 nonsingular_change5_curve5) =
        .some 2 0 nonsingular_curve5 := by
  refine ⟨rfl, ?_⟩
  rw [Affine.Point.variableChangeEquiv_some, Affine.Point.some.injEq]
  decide

/-- The variable change `(u, r, s, t) = (2, 1, 3, 4)` over `ℚ`. -/
private def changeQ : VariableChange ℚ :=
  ⟨⟨2, 2⁻¹, by norm_num, by norm_num⟩, 1, 3, 4⟩

/-- The test curve `y² = x³ + 1` over `ℚ`. -/
private def curveQ : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, 0, 1⟩

/-- The point `(1/4, -1/2)` of the transformed curve `changeQ • curveQ`. -/
private theorem nonsingular_changeQ_curveQ :
    (changeQ • curveQ).toAffine.Nonsingular (1 / 4) (-1 / 2) := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  norm_num [changeQ, curveQ, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆]

/-- The point `(2, 3)` of `y² = x³ + 1`. -/
private theorem nonsingular_curveQ : curveQ.toAffine.Nonsingular 2 3 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  norm_num [curveQ]

/-- The equivalence on a point with nonzero coordinates, in both
directions: over `ℚ`, the variable change `(u, r, s, t) = (2, 1, 3, 4)`
sends the point `(1/4, -1/2)` of the transformed curve to the point
`(2, 3)` of `y² = x³ + 1`, and the inverse sends `(2, 3)` back. Since
`u² ≠ u⁻²` and `u³ ≠ u⁻³` here, both checks see which of `C` and `C⁻¹`
each direction uses. -/
example :
    Affine.Point.variableChangeEquiv changeQ curveQ
        (.some (1 / 4) (-1 / 2) nonsingular_changeQ_curveQ) =
      .some 2 3 nonsingular_curveQ ∧
    (Affine.Point.variableChangeEquiv changeQ curveQ).symm
        (.some 2 3 nonsingular_curveQ) =
      .some (1 / 4) (-1 / 2) nonsingular_changeQ_curveQ := by
  constructor
  · rw [Affine.Point.variableChangeEquiv_some, Affine.Point.some.injEq]
    norm_num [changeQ, VariableChange.mapAffineCoordinates]
  · rw [Affine.Point.variableChangeEquiv_symm_some, Affine.Point.some.injEq]
    norm_num [changeQ, VariableChange.mapAffineCoordinates, VariableChange.inv_def]

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointTransport
