/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MixedReducedPoincareKernels
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The [0,1] determinant transport is inverse dual of the shifted transport:
a shifted scalar 1/2 must become 2. The zero polarization on a genus-zero
curve does not admit O_C as a stable point: its actual Euler characteristic
is one, while the required total polarization weight is zero.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PositiveCurveDeterminants SchemeDeterminantPresentations TwoTermDeterminantModels
open CoherentCurveLinearSeries NumericalCompactifiedJacobians

example {R : CommRingCat.{0}} (S : TransportSystem R) (P Q : LocalComplex R)
    (e : P.derivedObject ≅ Q.derivedObject) (f : Module.Dual R P.determinant) (x : P.determinant) :
    ((positiveTransport S P Q e).hom.hom f) (S.transport P.presentation Q.presentation e x) =
      f x := by
  change (S.transport P.presentation Q.presentation e).symm.dualMap f
    (S.transport P.presentation Q.presentation e x) = f x
  rw [LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]

private def half : ℚ ≃ₗ[ℚ] ℚ where
  toFun x := x / 2
  invFun x := 2 * x
  left_inv x := by ring
  right_inv x := by ring
  map_add' x y := by ring
  map_smul' r x := by simp only [smul_eq_mul, RingHom.id_apply]; ring

example : half.symm.dualMap (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 1 = 2 := by
  norm_num [LinearEquiv.dualMap_apply, half]

example {k : Type} [Field k] (C : Over (Spec (.of k))) [IsProperCurve C.hom]
    [TorsionFreeRestrictions C.left]
    (genus_zero_euler : ∀ hO, euler C.hom (structureModule C.left) hO = 1) :
    ¬ IsStable C (0 : Polarization C.left) (structureModule C.left) := by
  rintro ⟨hO, h⟩
  have he := h.2.2.1
  simp [totalWeight, genus_zero_euler hO] at he
