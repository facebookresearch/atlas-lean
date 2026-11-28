/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.TensorProduct.ZModRestrictNaturality
public import MathlibExt.LinearAlgebra.TensorProduct.LiftedZModInteger
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public meta import Mathlib.Tactic.NormNum

/-!
# Nonzero residue tensor classes and coefficient naturality

The class of `1 ⊗ 3` over the integers maps to a class detected as `3` in `ZMod 4`.
It is nonzero although multiplication by four kills it. The two coefficient maps multiply
by two and three and change both carrier universes. Both sides of the canonical naturality
square have the same nonzero coordinate `2`.

A copy of the residue ring in a higher universe gives the same integer tensor class.
The modulus-zero example retains ordinary integer multiplication.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped TensorProduct

namespace ZModScalarRestrictionTests

private abbrev R := ZMod 4
private abbrev L := ULift.{0} R
private abbrev N := ULift.{1} R
private abbrev L' := ULift.{2} R
private abbrev N' := ULift.{3} R
private abbrev E := ULift.{4} R

private def x : L := ULift.up 1
private def y : N := ULift.up 3

private def forward : L ⊗[ℤ] N ≃ₗ[ℤ] L ⊗[R] N :=
  TensorProduct.zmodRestrictIntEquiv 4 L N

private def detector : L ⊗[R] N →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap.comp
    (TensorProduct.map (ULift.moduleEquiv : L ≃ₗ[R] R).toLinearMap
      (ULift.moduleEquiv : N ≃ₗ[R] R).toLinearMap)

private theorem forward_coordinate : detector (forward (x ⊗ₜ[ℤ] y)) = 3 := by
  simp [forward, detector, x, y]

example : forward (x ⊗ₜ[ℤ] y) ≠ 0 := by
  intro h
  have h' := congrArg detector h
  rw [forward_coordinate, map_zero] at h'
  exact (by decide : (3 : R) ≠ 0) h'

private theorem integer_class_ne_zero : (x ⊗ₜ[ℤ] y : L ⊗[ℤ] N) ≠ 0 := by
  intro h
  have h' := congrArg (fun z => detector (forward z)) h
  rw [forward_coordinate, map_zero, map_zero] at h'
  exact (by decide : (3 : R) ≠ 0) h'

example : (4 : ℕ) • (x ⊗ₜ[ℤ] y : L ⊗[ℤ] N) = 0 :=
  TensorProduct.intTensor_nsmul_eq_zero 4 L N (x ⊗ₜ[ℤ] y)

example : forward.symm (x ⊗ₜ[R] y) = x ⊗ₜ[ℤ] y := by
  exact TensorProduct.zmodRestrictIntEquiv_symm_apply_tmul 4 L N x y

private def f : L →ₗ[R] L' :=
  (ULift.moduleEquiv : L' ≃ₗ[R] R).symm.toLinearMap.comp
    ((2 : R) • (ULift.moduleEquiv : L ≃ₗ[R] R).toLinearMap)

private def g : N →ₗ[R] N' :=
  (ULift.moduleEquiv : N' ≃ₗ[R] R).symm.toLinearMap.comp
    ((3 : R) • (ULift.moduleEquiv : N ≃ₗ[R] R).toLinearMap)

private def top : L ⊗[ℤ] N →ₗ[ℤ] L' ⊗[R] N' :=
  (TensorProduct.map f g).toAddMonoidHom.toIntLinearMap.comp forward.toLinearMap

private def bottom : L ⊗[ℤ] N →ₗ[ℤ] L' ⊗[R] N' :=
  (TensorProduct.zmodRestrictIntEquiv 4 L' N').toLinearMap.comp
    (TensorProduct.map f.toAddMonoidHom.toIntLinearMap g.toAddMonoidHom.toIntLinearMap)

private theorem naturality : top = bottom :=
  TensorProduct.zmodRestrictIntEquiv_naturality 4 f g

private def targetDetector : L' ⊗[R] N' →ₗ[R] R :=
  (TensorProduct.lid R R).toLinearMap.comp
    (TensorProduct.map (ULift.moduleEquiv : L' ≃ₗ[R] R).toLinearMap
      (ULift.moduleEquiv : N' ≃ₗ[R] R).toLinearMap)

private theorem top_coordinate : targetDetector (top (x ⊗ₜ[ℤ] y)) = 2 := by
  change (2 : R) * (3 * 3) = 2
  norm_num [R]

example : targetDetector (bottom (x ⊗ₜ[ℤ] y)) = 2 := by
  rw [← naturality]
  exact top_coordinate

example : top (x ⊗ₜ[ℤ] y) ≠ 0 := by
  intro h
  have h' := congrArg targetDetector h
  rw [top_coordinate, map_zero] at h'
  exact (by decide : (2 : R) ≠ 0) h'

example : bottom (x ⊗ₜ[ℤ] y) ≠ 0 := by
  rw [← naturality]
  intro h
  have h' := congrArg targetDetector h
  rw [top_coordinate, map_zero] at h'
  exact (by decide : (2 : R) ≠ 0) h'

private def liftedForward : L ⊗[E] N ≃ₗ[ℤ] L ⊗[ℤ] N :=
  ScalarRestriction.liftedZModIntegerTensorEquiv.{0, 1, 4} 4 L N

example : liftedForward (x ⊗ₜ[E] y) = x ⊗ₜ[ℤ] y :=
  ScalarRestriction.liftedZModIntegerTensorEquiv_tmul.{0, 1, 4} 4 L N x y

example : (x ⊗ₜ[E] y : L ⊗[E] N) ≠ 0 := by
  intro h
  have h' := congrArg liftedForward h
  simp only [liftedForward, ScalarRestriction.liftedZModIntegerTensorEquiv_tmul,
    map_zero] at h'
  exact integer_class_ne_zero h'

private instance : Module (ZMod 0) ℤ :=
  AddCommGroup.zmodModule (n := 0) (fun z : ℤ => zero_nsmul z)

example :
    (TensorProduct.lid ℤ ℤ)
      (TensorProduct.zmodRestrictIntEquiv 0 ℤ ℤ ((5 : ℤ) ⊗ₜ[ℤ] (7 : ℤ))) = 35 := by
  rw [TensorProduct.zmodRestrictIntEquiv_apply_tmul]
  change (5 : ℤ) * 7 = 35
  norm_num

end ZModScalarRestrictionTests
