/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Original tensor Čech exactness under faithfully flat scalar extension

The unit sends m to 1 tensor m. The original overlap difference sends
b tensor m to b tensor (1 tensor m) minus 1 tensor (b tensor m).
After genuine scalar extension, multiplication of the first two coefficients
contracts the complex. Faithful flatness reflects its exactness.
-/

@[expose] public section
noncomputable section

namespace TensorProduct

open scoped TensorProduct

universe u v w
variable (A : Type u) (B : Type v) (M : Type w)
variable [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

/-- The original coefficient-tensor unit. -/
def cechUnit : M →ₗ[A] B ⊗[A] M := TensorProduct.mk A B M 1

/-- The actual difference of the two original tensor overlap maps, in source order. -/
def cechDifference : (B ⊗[A] M) →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (cechUnit A B M).lTensor B - TensorProduct.mk A B (B ⊗[A] M) 1

/-- The overlap difference retains its two actual tensor values with the original sign. -/
theorem cechDifference_tmul (b : B) (m : M) :
    cechDifference A B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := by
  rw [cechDifference, LinearMap.sub_apply, LinearMap.lTensor_tmul]
  rfl

/-- Actual multiplication of the outer tensor coefficient on the original scalar-extended module. -/
def cechScalarAction : B ⊗[A] (B ⊗[A] M) →ₗ[A] B ⊗[A] M :=
  ((LinearMap.id : (B ⊗[A] M) →ₗ[A] B ⊗[A] M).liftBaseChange B).restrictScalars A

/-- The actual coefficient contraction multiplies the first two coefficients, preserving the original module. -/
theorem cechScalarAction_tmul (b c : B) (m : M) :
    cechScalarAction A B M (b ⊗ₜ[A] (c ⊗ₜ[A] m)) = (b * c) ⊗ₜ[A] m := by
  rw [cechScalarAction, LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul,
    LinearMap.id_apply, TensorProduct.smul_tmul', smul_eq_mul]

/-- The original tensor overlap difference annihilates the original tensor unit. -/
theorem cechDifference_comp_unit : (cechDifference A B M).comp (cechUnit A B M) = 0 := by
  apply LinearMap.ext
  intro m
  change cechDifference A B M ((1 : B) ⊗ₜ[A] m) = 0
  rw [cechDifference_tmul, sub_self]

/-- Multiplying the first two coefficients contracts the genuine scalar-extended overlap differential. -/
theorem cechScalarAction_comp_lTensor_difference :
    (cechScalarAction A B (B ⊗[A] M)).comp ((cechDifference A B M).lTensor B) =
      ((cechUnit A B M).lTensor B).comp (cechScalarAction A B M) - LinearMap.id := by
  apply TensorProduct.ext'
  intro b x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at hx hy ⊢
    rw [hx, hy]
  | tmul c m =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.lTensor_tmul, cechDifference_tmul, TensorProduct.tmul_sub, map_sub,
      cechScalarAction_tmul, cechUnit, TensorProduct.mk_apply, mul_one]

/-- The original tensor Čech complex is exact after actual scalar extension. -/
theorem cech_lTensor_exact :
    Function.Exact ((cechUnit A B M).lTensor B) ((cechDifference A B M).lTensor B) := by
  have hcomp : ((cechDifference A B M).lTensor B).comp ((cechUnit A B M).lTensor B) = 0 := by
    rw [← LinearMap.lTensor_comp, cechDifference_comp_unit, LinearMap.lTensor_zero]
  intro x
  constructor
  · intro hx
    refine ⟨cechScalarAction A B M x, ?_⟩
    have h := LinearMap.congr_fun (cechScalarAction_comp_lTensor_difference A B M) x
    change cechScalarAction A B (B ⊗[A] M) ((cechDifference A B M).lTensor B x) =
      (cechUnit A B M).lTensor B (cechScalarAction A B M x) - x at h
    rw [hx, map_zero] at h
    exact sub_eq_zero.mp h.symm
  · rintro ⟨y, hy⟩
    rw [← hy]
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hcomp y

/-- Faithful flatness reflects the exactness of the original, unaltered tensor Čech complex. -/
theorem cech_exact [Module.FaithfullyFlat A B] :
    Function.Exact (cechUnit A B M) (cechDifference A B M) :=
  Module.FaithfullyFlat.lTensor_reflects_exact A B (cechUnit A B M) (cechDifference A B M)
    (cech_lTensor_exact A B M)

/-- The original module injects through its actual tensor unit under faithful flatness. -/
theorem cechUnit_injective [Module.FaithfullyFlat A B] : Function.Injective (cechUnit A B M) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective M

end TensorProduct
