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
# Čech tensor exactness for faithfully flat scalars

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). The complex M→ηB⊗M→δB⊗B⊗M becomes
split exact after tensoring by B. If B is faithfully flat over A, η is injective and
range(η)=ker(δ).
-/

@[expose] public section
noncomputable section

namespace TensorProduct

open scoped TensorProduct

universe u v w
variable (A : Type u) (B : Type v) (M : Type w)
variable [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

/-- **Tensor unit of the Čech complex.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). The A-linear map cechUnit A B M
is η:m↦1⊗m.
-/
def cechUnit : M →ₗ[A] B ⊗[A] M := TensorProduct.mk A B M 1

/-- **Difference of the two Čech overlap maps.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). The A-linear map cechDifference A
B M is δ with this ordered difference.
-/
def cechDifference : (B ⊗[A] M) →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (cechUnit A B M).lTensor B - TensorProduct.mk A B (B ⊗[A] M) 1

/-- **Pure tensor formula for the Čech difference.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). For b∈B,m∈M,
cechDifference(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m).
-/
theorem cechDifference_tmul (b : B) (m : M) :
    cechDifference A B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := by
  rw [cechDifference, LinearMap.sub_apply, LinearMap.lTensor_tmul]
  rfl

/-- **Multiplication contraction of the outer Čech coefficients.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). The A-linear map
cechScalarAction:B⊗(B⊗M)→B⊗M sends b⊗(c⊗m) to bc⊗m.
-/
def cechScalarAction : B ⊗[A] (B ⊗[A] M) →ₗ[A] B ⊗[A] M :=
  ((LinearMap.id : (B ⊗[A] M) →ₗ[A] B ⊗[A] M).liftBaseChange B).restrictScalars A

/-- **Pure tensor value of the Čech coefficient contraction.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). For b,c∈B,m∈M,
cechScalarAction(b⊗(c⊗m))=(b*c)⊗m.
-/
theorem cechScalarAction_tmul (b c : B) (m : M) :
    cechScalarAction A B M (b ⊗ₜ[A] (c ⊗ₜ[A] m)) = (b * c) ⊗ₜ[A] m := by
  rw [cechScalarAction, LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul,
    LinearMap.id_apply, TensorProduct.smul_tmul', smul_eq_mul]

/-- **Čech overlap difference kills the tensor unit.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). The identity
cechDifference∘cechUnit=0 is δ∘η=0.
-/
theorem cechDifference_comp_unit : (cechDifference A B M).comp (cechUnit A B M) = 0 := by
  apply LinearMap.ext
  intro m
  change cechDifference A B M ((1 : B) ⊗ₜ[A] m) = 0
  rw [cechDifference_tmul, sub_self]

/-- **Contraction identity after one scalar extension.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). Let μ_M:B⊗B⊗M→B⊗M multiply the
first two coefficients. Then μ_(B⊗M)∘(id_B⊗δ)=(id_B⊗η)∘μ_M-id_(B⊗B⊗M).
-/
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

/-- **Čech exactness after tensoring once by the algebra.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). The scalar-extended sequence
B⊗M→id⊗ηB⊗B⊗M→id⊗δB⊗B⊗B⊗M is exact.
-/
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

/-- **Faithful flatness reflects Čech exactness.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). If B is faithfully flat as an
A-module, range(η)=ker(δ).
-/
theorem cech_exact [Module.FaithfullyFlat A B] :
    Function.Exact (cechUnit A B M) (cechDifference A B M) :=
  Module.FaithfullyFlat.lTensor_reflects_exact A B (cechUnit A B M) (cechDifference A B M)
    (cech_lTensor_exact A B M)

/-- **Tensor-unit injection under faithfully flat scalars.**

Let A,B be commutative rings with an A-algebra structure on B, and M an A-module. Define
η(m)=1⊗m in B⊗_AM and δ(b⊗m)=b⊗(1⊗m)-1⊗(b⊗m) in B⊗_A(B⊗_AM). If B is faithfully flat over A,
cechUnit A B M:m↦1⊗m is injective.
-/
theorem cechUnit_injective [Module.FaithfullyFlat A B] : Function.Injective (cechUnit A B M) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective M

end TensorProduct
