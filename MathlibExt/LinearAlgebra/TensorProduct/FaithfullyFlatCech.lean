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
# The initial tensor Čech sequence for a faithfully flat algebra

Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module, in independent scalar and carrier universes.
The unit η : M → B ⊗[A] M sends m to 1 ⊗ m. The overlap difference is
δ(b ⊗ m) = b ⊗ (1 ⊗ m) - 1 ⊗ (b ⊗ m),
and δ ∘ η = 0.

After tensoring with B, multiplying the first two B-coefficients gives
a contraction identity and exactness at the scalar-extended middle term.
If B is faithfully flat over A, the original sequence is exact at
B ⊗[A] M and η is injective. No flatness condition on M is required.
-/

@[expose] public section
noncomputable section

namespace TensorProduct

open scoped TensorProduct

universe u v w
variable (A : Type u) (B : Type v) (M : Type w)
variable [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
The tensor Čech unit is the A-linear map η : M → B ⊗[A] M
with value η(m) = 1 ⊗ m. -/
def cechUnit : M →ₗ[A] B ⊗[A] M := TensorProduct.mk A B M 1

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
The A-linear overlap difference δ : B ⊗[A] M → B ⊗[A] (B ⊗[A] M)
is the difference of inserting 1 in the second and first B positions.
Its pure value is b ⊗ (1 ⊗ m) - 1 ⊗ (b ⊗ m). -/
def cechDifference : (B ⊗[A] M) →ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  (cechUnit A B M).lTensor B - TensorProduct.mk A B (B ⊗[A] M) 1

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
On a pure tensor b ⊗ m, the overlap map has the signed value
δ(b ⊗ m) = b ⊗ (1 ⊗ m) - 1 ⊗ (b ⊗ m). -/
theorem cechDifference_tmul (b : B) (m : M) :
    cechDifference A B M (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m) - (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] m) := by
  rw [cechDifference, LinearMap.sub_apply, LinearMap.lTensor_tmul]
  rfl

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
The A-linear contraction h : B ⊗[A] (B ⊗[A] M) → B ⊗[A] M
multiplies the first two coefficient factors: h(b ⊗ (c ⊗ m)) = bc ⊗ m. -/
def cechScalarAction : B ⊗[A] (B ⊗[A] M) →ₗ[A] B ⊗[A] M :=
  ((LinearMap.id : (B ⊗[A] M) →ₗ[A] B ⊗[A] M).liftBaseChange B).restrictScalars A

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
The contraction has pure value h(b ⊗ (c ⊗ m)) = (bc) ⊗ m,
with multiplication in the order of the first and second B-coefficients. -/
theorem cechScalarAction_tmul (b c : B) (m : M) :
    cechScalarAction A B M (b ⊗ₜ[A] (c ⊗ₜ[A] m)) = (b * c) ⊗ₜ[A] m := by
  rw [cechScalarAction, LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul,
    LinearMap.id_apply, TensorProduct.smul_tmul', smul_eq_mul]

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
For η(m) = 1 ⊗ m and
δ(b ⊗ m) = b ⊗ (1 ⊗ m) - 1 ⊗ (b ⊗ m), the composite δ ∘ η is zero.
Thus these two maps form a complex. -/
theorem cechDifference_comp_unit : (cechDifference A B M).comp (cechUnit A B M) = 0 := by
  apply LinearMap.ext
  intro m
  change cechDifference A B M ((1 : B) ⊗ₜ[A] m) = 0
  rw [cechDifference_tmul, sub_self]

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
Write η_B = id_B ⊗ η and δ_B = id_B ⊗ δ.
Let h₁ multiply the first two B-coefficients in B ⊗ (B ⊗ M),
and h₂ do so in B ⊗ (B ⊗ (B ⊗ M)).
The contraction identity is h₂ ∘ δ_B = η_B ∘ h₁ - id
on B ⊗ (B ⊗ M), with all tensors over A. -/
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

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
The maps id_B ⊗ η and id_B ⊗ δ are exact at B ⊗[A] (B ⊗[A] M):
the image of the scalar-extended unit equals the kernel of the
scalar-extended overlap difference. This statement needs no
flatness hypothesis on B or M. -/
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

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
If B is faithfully flat over A, η : M → B ⊗[A] M and
δ : B ⊗[A] M → B ⊗[A] (B ⊗[A] M) are exact at B ⊗[A] M:
im η = ker δ. -/
theorem cech_exact [Module.FaithfullyFlat A B] :
    Function.Exact (cechUnit A B M) (cechDifference A B M) :=
  Module.FaithfullyFlat.lTensor_reflects_exact A B (cechUnit A B M) (cechDifference A B M)
    (cech_lTensor_exact A B M)

/-- Let A and B be commutative rings with an A-algebra structure on B,
and M an A-module with additive commutative group structure.
If B is faithfully flat over A, the unit m ↦ 1 ⊗ m from M
to B ⊗[A] M is injective. -/
theorem cechUnit_injective [Module.FaithfullyFlat A B] : Function.Injective (cechUnit A B M) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective M

end TensorProduct
