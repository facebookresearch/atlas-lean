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

/-- `mapPoint` is Mathlib's `Affine.Point.map` for the `F`-algebra structure `f.toAlgebra`
on `k`, read on `W₀.toAffine.Point`, the self-base-change `(W₀.toAffine⁄F).Point`. -/
example :
    letI := f.toAlgebra
    (mapPoint f : W₀.toAffine.Point →+ (W₀.map f).toAffine.Point) =
      Affine.Point.map (W' := W₀.toAffine) (Algebra.ofId F k) :=
  rfl

/-- Mathlib's generic lemmas for additive homomorphisms give the laws of `mapPoint`: it
preserves zero, addition, negation and natural and integer scalar multiples, and, being
injective, additive order. -/
example (P Q : W₀.toAffine.Point) (n : ℕ) (m : ℤ) :
    mapPoint f (0 : W₀.toAffine.Point) = 0 ∧ mapPoint f (P + Q) = mapPoint f P + mapPoint f Q ∧
      mapPoint f (-P) = -mapPoint f P ∧ mapPoint f (n • P) = n • mapPoint f P ∧
        mapPoint f (m • P) = m • mapPoint f P ∧ addOrderOf (mapPoint f P) = addOrderOf P :=
  ⟨map_zero (mapPoint f), map_add (mapPoint f) P Q, map_neg (mapPoint f) P,
    map_nsmul (mapPoint f) n P, map_zsmul (mapPoint f) m P,
    addOrderOf_injective (mapPoint f) (mapPoint_injective f) P⟩

/-- `simp` normalizes `mapPoint` of zero, sums and negatives with the generic lemmas. -/
example (P Q : W₀.toAffine.Point) :
    mapPoint f (P + -Q + 0) = mapPoint f P + -mapPoint f Q := by
  simp

/-- `mapPoint` also takes an endomorphism `σ : F →+* F`, where `σ.toAlgebra` would clash with
`Algebra.id F`; the generic lemmas apply to it unchanged. -/
example (σ : F →+* F) (P Q : W₀.toAffine.Point) :
    mapPoint σ (P + Q) = mapPoint σ P + mapPoint σ Q ∧
      Function.Injective (mapPoint σ (W₀ := W₀)) :=
  ⟨map_add (mapPoint σ) P Q, mapPoint_injective σ⟩

/-- The additive equivalence from an equality of curves is the
identity on the diagonal. -/
example (W : WeierstrassCurve F) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ :=
  pointAddEquivOfEq_refl W

/-- Application consumer, with no decidability assumption: for a curve `V`
with `C • W = V`, the transport sends an affine point `(x, y)` of `V` to
`(u²x + r, u³y + u²sx + t)`. -/
example {K : Type u} [Field K] (C : VariableChange K) (W V : WeierstrassCurve K)
    (hV : C • W = V) {x y : K} (h : V.toAffine.Nonsingular x y) :
    Affine.Point.equivOfVariableChangeEq hV (.some x y h) =
      .some ((C.u : K) ^ 2 * x + C.r)
        ((C.u : K) ^ 3 * y + (C.u : K) ^ 2 * C.s * x + C.t)
        ((VariableChange.nonsingular_mapAffineCoordinates_iff C W (x, y)).mp (hV ▸ h)) :=
  Affine.Point.equivOfVariableChangeEq_some hV h

/-- With `h := rfl` the transport is the underlying equivalence of
`Affine.Point.variableChangeAddEquiv`, taken with classical decidability. -/
example {K : Type u} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) :
    open scoped Classical in
    Affine.Point.equivOfVariableChangeEq (rfl : C • W = C • W) =
      (Affine.Point.variableChangeAddEquiv C W).toEquiv :=
  rfl

/-- On an elliptic curve, the transport along `rfl` is the existing
elliptic-curve point equivalence `VariableChange.pointEquiv`. -/
example {K : Type u} [Field K] (C : VariableChange K)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Affine.Point.equivOfVariableChangeEq (rfl : C • W = C • W) =
      VariableChange.pointEquiv C W := by
  ext P
  rcases P with _ | ⟨x, y, h⟩
  · exact Affine.Point.equivOfVariableChangeEq_zero rfl
  · exact Affine.Point.equivOfVariableChangeEq_some rfl h

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Translation by one in the affine `x` coordinate. -/
private def change5 : VariableChange (ZMod 5) :=
  ⟨1, 1, 0, 0⟩

/-- The test curve `y² = x³ + x` over `ZMod 5`. -/
private def curve5 : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, 1, 0⟩

/-- The translated curve `y² = x³ + 3x² + 4x + 2`, given by its own coefficients. -/
private def curve5' : WeierstrassCurve (ZMod 5) :=
  ⟨0, 3, 0, 4, 2⟩

/-- `curve5'` is the translate of `curve5` by `change5`. -/
private theorem change5_smul_curve5 : change5 • curve5 = curve5' := by
  ext <;> decide

/-- The point `(1, 0)` of `curve5'`. -/
private theorem nonsingular_curve5' : curve5'.toAffine.Nonsingular 1 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  decide

/-- The point `(2, 0)` of `y² = x³ + x`. -/
private theorem nonsingular_curve5 : curve5.toAffine.Nonsingular 2 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  decide

/-- A nontrivial instance of the transport: translation by `1` in the
`x`-coordinate, from the curve `curve5'` given by its own coefficients
to `y² = x³ + x` over `ZMod 5`, fixes the zero point and sends `(1, 0)`
to `(2, 0)`. -/
example :
    Affine.Point.equivOfVariableChangeEq change5_smul_curve5 0 = 0 ∧
      Affine.Point.equivOfVariableChangeEq change5_smul_curve5
          (.some 1 0 nonsingular_curve5') =
        .some 2 0 nonsingular_curve5 := by
  refine ⟨Affine.Point.equivOfVariableChangeEq_zero _, ?_⟩
  rw [Affine.Point.equivOfVariableChangeEq_some, Affine.Point.some.injEq]
  decide

/-- The variable change `(u, r, s, t) = (2, 1, 3, 4)` over `ℚ`. -/
private def changeQ : VariableChange ℚ :=
  ⟨⟨2, 2⁻¹, by norm_num, by norm_num⟩, 1, 3, 4⟩

/-- The test curve `y² = x³ + 1` over `ℚ`. -/
private def curveQ : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, 0, 1⟩

/-- The transformed curve `y² + 3xy + y = x³ - 3/2 x² - 21/16 x - 7/32`,
given by its own coefficients. -/
private def curveQ' : WeierstrassCurve ℚ :=
  ⟨3, -3 / 2, 1, -21 / 16, -7 / 32⟩

/-- `curveQ'` is `changeQ • curveQ`. -/
private theorem changeQ_smul_curveQ : changeQ • curveQ = curveQ' := by
  ext <;> norm_num [changeQ, curveQ, curveQ', variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆]

/-- The point `(1/4, -1/2)` of `curveQ'`. -/
private theorem nonsingular_curveQ' : curveQ'.toAffine.Nonsingular (1 / 4) (-1 / 2) := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  norm_num [curveQ']

/-- The point `(2, 3)` of `y² = x³ + 1`. -/
private theorem nonsingular_curveQ : curveQ.toAffine.Nonsingular 2 3 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  norm_num [curveQ]

/-- The transport on a point with nonzero coordinates, in both directions:
over `ℚ`, with `(u, r, s, t) = (2, 1, 3, 4)`, the point `(1/4, -1/2)` of
`curveQ'` goes to the point `(2, 3)` of `y² = x³ + 1`, and the inverse
sends `(2, 3)` back. Since `u² ≠ u⁻²` and `u³ ≠ u⁻³` here, the check sees
that the forward map uses the coordinate map of `C`, not of `C⁻¹`. -/
example :
    Affine.Point.equivOfVariableChangeEq changeQ_smul_curveQ
        (.some (1 / 4) (-1 / 2) nonsingular_curveQ') =
      .some 2 3 nonsingular_curveQ ∧
    (Affine.Point.equivOfVariableChangeEq changeQ_smul_curveQ).symm
        (.some 2 3 nonsingular_curveQ) =
      .some (1 / 4) (-1 / 2) nonsingular_curveQ' := by
  have h : Affine.Point.equivOfVariableChangeEq changeQ_smul_curveQ
      (.some (1 / 4) (-1 / 2) nonsingular_curveQ') = .some 2 3 nonsingular_curveQ := by
    rw [Affine.Point.equivOfVariableChangeEq_some, Affine.Point.some.injEq]
    norm_num [changeQ, VariableChange.mapAffineCoordinates]
  exact ⟨h, (Equiv.symm_apply_eq _).mpr h.symm⟩

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.PointTransport
