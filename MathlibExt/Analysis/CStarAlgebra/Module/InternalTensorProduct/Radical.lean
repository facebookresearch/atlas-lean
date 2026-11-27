/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Algebraic

/-!
# Radical quotient of balanced algebraic C-star module tensors

The radical is the actual semilinear kernel of the balanced inner form.
Conjugate symmetry gives annihilation in both slots, and the existing right
coefficient action preserves this kernel. The quotient action and sesquilinear
form below are therefore constructed by the ordinary algebraic quotient API.

No positivity, completeness or Cauchy–Schwarz assumption is added. This is the
radical quotient, not yet Blackadar's quotient by all self-inner-zero vectors:
that identification requires the positive common-finite-Gram argument. No norm,
definiteness, completion, completed-model witness or global instance is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [AddCommGroup E₁] [Module ℂ E₁] [Norm E₁]
variable [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
variable [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. The radical is the complex-linear subspace of balanced tensors
whose inner product against every balanced tensor vanishes. -/
def radicalSpace
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    Submodule ℂ (BalancedTensor (E₁ := E₁) φ) :=
  LinearMap.ker (balancedInner (E₁ := E₁) φ)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. A balanced tensor is in the radical exactly when its inner
product against every balanced tensor vanishes. -/
@[simp]
theorem mem_radicalSpace_iff
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z : BalancedTensor (E₁ := E₁) φ) :
    z ∈ radicalSpace φ ↔ ∀ w, balancedInner φ z w = 0 := by
  rw [radicalSpace, LinearMap.mem_ker]
  constructor
  · intro hz w
    simpa only [LinearMap.zero_apply] using
      congrArg (fun L : BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] B₂ => L w) hz
  · intro hz
    exact LinearMap.ext hz

private theorem radicalSpace_le_ker_balancedInner_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z : BalancedTensor (E₁ := E₁) φ) :
    radicalSpace φ ≤ LinearMap.ker (balancedInner φ z) := by
  intro w hw
  change balancedInner φ z w = 0
  apply star_injective
  simpa only [star_balancedInner, star_zero] using
    (mem_radicalSpace_iff φ w).mp hw z

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. Right multiplication by any B₂ coefficient preserves the radical. -/
theorem radicalSpace_balancedRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b : B₂) :
    radicalSpace (E₁ := E₁) φ ≤ (radicalSpace φ).comap (balancedRightSMul φ b) := by
  intro z hz
  change balancedRightSMul φ b z ∈ radicalSpace φ
  apply (mem_radicalSpace_iff φ _).mpr
  intro w
  have h : balancedInner φ w z = 0 :=
    radicalSpace_le_ker_balancedInner_right φ w hz
  apply star_injective
  rw [star_balancedInner, star_zero, balancedInner_balancedRightSMul, h, zero_mul]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. The radical tensor space is the balanced algebraic tensor
quotient modulo the radical of its coefficient-valued inner form. -/
abbrev RadicalTensor
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :=
  BalancedTensor (E₁ := E₁) φ ⧸ radicalSpace (E₁ := E₁) φ

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. Right coefficient multiplication descends to a complex-linear map
on the radical quotient. -/
def radicalRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b : B₂) :
    RadicalTensor (E₁ := E₁) φ →ₗ[ℂ] RadicalTensor (E₁ := E₁) φ :=
  (radicalSpace φ).mapQ (radicalSpace φ) (balancedRightSMul φ b)
    (radicalSpace_balancedRightSMul φ b)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. Right multiplication of a radical-quotient class is the class of
the right-multiplied representative. -/
theorem radicalRightSMul_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b : B₂)
    (z : BalancedTensor (E₁ := E₁) φ) :
    radicalRightSMul φ b ((radicalSpace φ).mkQ z) =
      (radicalSpace φ).mkQ (balancedRightSMul φ b z) := by
  simp only [radicalRightSMul, Submodule.mkQ_apply, Submodule.mapQ_apply]

theorem radicalRightSMul_zero
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    radicalRightSMul (E₁ := E₁) φ (0 : B₂) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  simp only [radicalRightSMul_mkQ, balancedRightSMul_zero,
    LinearMap.zero_apply, map_zero]

theorem radicalRightSMul_add
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b c : B₂) :
    radicalRightSMul (E₁ := E₁) φ (b + c) =
      radicalRightSMul φ b + radicalRightSMul φ c := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  simp only [radicalRightSMul_mkQ, balancedRightSMul_add, LinearMap.add_apply, map_add]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. Right multiplication by a product of coefficients agrees with the
successive right multiplications in the right-action order. -/
theorem radicalRightSMul_mul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b c : B₂) :
    radicalRightSMul (E₁ := E₁) φ (b * c) =
      (radicalRightSMul φ c).comp (radicalRightSMul φ b) := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  simp only [radicalRightSMul_mkQ, balancedRightSMul_mul, LinearMap.comp_apply]

theorem radicalRightSMul_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (c : ℂ) (b : B₂) :
    radicalRightSMul (E₁ := E₁) φ (c • b) = c • radicalRightSMul φ b := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  simp only [radicalRightSMul_mkQ, balancedRightSMul_smul, LinearMap.smul_apply, map_smul]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. The radical tensor quotient carries the right B₂ action induced
by the balanced tensor action. -/
@[instance_reducible]
def radicalRightAction
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) where
  smul b q := radicalRightSMul φ b.unop q

private def rightRadicalInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    BalancedTensor (E₁ := E₁) φ →ₗ⋆[ℂ]
      RadicalTensor (E₁ := E₁) φ →ₗ[ℂ] B₂ where
  toFun z := (radicalSpace φ).liftQ (balancedInner φ z)
    (radicalSpace_le_ker_balancedInner_right φ z)
  map_add' := by
    intro z w
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
    simpa only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.add_apply] using
      balancedInner_add_left φ z w v
  map_smul' := by
    intro c z
    apply LinearMap.ext
    intro q
    obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
    simpa only [Submodule.mkQ_apply, Submodule.liftQ_apply,
      LinearMap.smul_apply, starRingEnd_apply] using balancedInner_smul_left φ c z w

private theorem radicalSpace_le_ker_rightRadicalInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    radicalSpace (E₁ := E₁) φ ≤ LinearMap.ker (rightRadicalInner φ) := by
  intro z hz
  change rightRadicalInner φ z = 0
  apply LinearMap.ext
  intro q
  obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  simpa only [rightRadicalInner, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.zero_apply] using
    (mem_radicalSpace_iff φ z).mp hz w

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. The balanced coefficient-valued inner form descends to a
conjugate-symmetric sesquilinear form on the radical quotient. -/
@[no_expose]
def radicalInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    RadicalTensor (E₁ := E₁) φ →ₗ⋆[ℂ]
      RadicalTensor (E₁ := E₁) φ →ₗ[ℂ] B₂ :=
  (radicalSpace φ).liftQ (rightRadicalInner φ)
    (radicalSpace_le_ker_rightRadicalInner φ)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. The descended inner product of two quotient classes equals the
balanced inner product of their representatives. -/
theorem radicalInner_mkQ_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w : BalancedTensor (E₁ := E₁) φ) :
    radicalInner φ ((radicalSpace φ).mkQ z) ((radicalSpace φ).mkQ w) =
      balancedInner φ z w := by
  simp only [radicalInner, rightRadicalInner, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. Interchanging the two arguments of the radical inner form takes
its coefficient involution. -/
theorem star_radicalInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w : RadicalTensor (E₁ := E₁) φ) :
    star (radicalInner φ z w) = radicalInner φ w z := by
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective w
  simpa only [radicalInner_mkQ_mkQ] using star_balancedInner φ z w

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. The radical inner form is linear for right B₂ multiplication in
its second argument. -/
theorem radicalInner_radicalRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w : RadicalTensor (E₁ := E₁) φ) (b : B₂) :
    radicalInner φ z (radicalRightSMul φ b w) = radicalInner φ z w * b := by
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective w
  simpa only [radicalRightSMul_mkQ, radicalInner_mkQ_mkQ] using
    balancedInner_balancedRightSMul φ z w b

end CStarModule.InternalTensorProduct
