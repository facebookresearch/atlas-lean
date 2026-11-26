/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.GenusOnePic0

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [GenusOnePlaceGate W]

example (P : W.Point) : (placeOfPoint (W := W) P).deg = 1 :=
  deg_placeOfPoint P

example (v : AlgebraicCurve.Place F W.FunctionField) : Module.Finite F v.ResidueField :=
  inferInstance

/-- Every place has degree one, so a single place with multiplicity `3` has degree `3`. -/
example (P : W.Point) :
    Divisor.degree (Finsupp.single (placeOfPoint P) 3 : AlgebraicCurve.Divisor F W.FunctionField)
      = 3 := by
  simp [Divisor.degree_single]

/-- `pointDivisor P` is the point difference of the places attached to `P` and `0`; neither it nor
`pointClass` needs decidable equality on `F`. -/
example (P : W.Point) :
    (pointDivisor P : AlgebraicCurve.Divisor F W.FunctionField) =
      CurveDivisor.pointDiff (placeOfPoint P) (placeOfPoint 0) :=
  rfl

example (P : W.Point) : pointClass P = Pic0.mk (pointDivisor P) := rfl

example : pointClass (0 : W.Point) = 0 := pointClass_zero

section DecidableEq

variable [DecidableEq F]

/-- `divisorSum` sends `n` times a place to `n` times the point attached to it. -/
example (v : AlgebraicCurve.Place F W.FunctionField) (n : ℤ) :
    divisorSum (Finsupp.single v n) = n • (pointEquivPlace (W := W)).symm v := by
  simp only [divisorSum, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

example (P : W.Point) :
    divisorSum (pointDivisor P : AlgebraicCurve.Divisor F W.FunctionField) = P :=
  divisorSum_pointDivisor P

/-- The divisor `(P) + (Q) - 2 (0)` sums to `P + Q`. -/
example (P Q : W.Point) :
    divisorSum (Finsupp.single (placeOfPoint P) 1 + Finsupp.single (placeOfPoint Q) 1 -
      Finsupp.single (placeOfPoint 0) 2 : AlgebraicCurve.Divisor F W.FunctionField) = P + Q := by
  rw [map_sub, map_add, divisorSum_single_placeOfPoint, divisorSum_single_placeOfPoint,
    divisorSum_single_placeOfPoint, one_smul, one_smul, smul_zero, sub_zero]

variable [AbelTheorem W]

example (P : W.Point) : pic0ToPoint (pointClass P) = P :=
  pic0ToPoint_pointClass P

example (P : W.Point) : (genusOnePic0Equiv W).symm P = pointClass P :=
  genusOnePic0Equiv_symm_apply P

example (P : W.Point) : genusOnePic0Equiv W (pointClass P) = P := by
  rw [genusOnePic0Equiv_apply, pic0ToPoint_pointClass]

example (P Q : W.Point) : pointClass (P + Q) = pointClass P + pointClass Q :=
  pointClass_add P Q

example (P : W.Point) : pointClass (-P) = -pointClass P := by
  rw [← genusOnePic0Equiv_symm_apply, map_neg, genusOnePic0Equiv_symm_apply]

/-- Abel's criterion read on `Pic0`: the class of a divisor of degree zero vanishes exactly when
the points attached to it sum to zero. -/
example (D : Divisor.degZero (K := F) (F := W.FunctionField)) :
    Pic0.mk D = 0 ↔ divisorSum (D : AlgebraicCurve.Divisor F W.FunctionField) = 0 := by
  rw [← pic0ToPoint_mk, ← genusOnePic0Equiv_apply, AddEquiv.map_eq_zero_iff]

end DecidableEq
