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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.NullSpace
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Positivity

/-!
# Actual pre-Hilbert data on the algebraic tensor null quotient

The chosen norm is exactly the square root of the norm of the actual quotient
self-inner. All inner/right-action fields are derived from the constructed
radical quotient and its self-null identification. The standard CStarModule
normed-space core supplies the normed dictionaries; no second triangle or
Cauchy–Schwarz framework is introduced.

Every structure below is named, locally activatable data, not a registered
norm/module/space instance. No completeness, completed model or Source
existence witness is supplied for the algebraic quotient.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂

section NormData

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [AddCommGroup E₁] [Module ℂ E₁] [Norm E₁]
variable [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
variable [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. The norm on the radical tensor quotient is the square root of the
norm of its coefficient-valued self-inner product. -/
@[instance_reducible]
def radicalTensorNorm
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    Norm (RadicalTensor (E₁ := E₁) φ) where
  norm q := Real.sqrt ‖radicalInner φ q q‖

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ a right pre-Hilbert B₁-module,
E₂ a normed right pre-Hilbert B₂-module, and φ a nonunital star representation of B₁ by
adjointable operators on E₂. The norm of a radical-quotient vector q equals the square root of
the norm of its coefficient-valued self-inner product. -/
@[simp]
theorem radicalTensorNorm_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (q : RadicalTensor (E₁ := E₁) φ) :
    letI : Norm (RadicalTensor (E₁ := E₁) φ) := radicalTensorNorm φ;
    ‖q‖ = Real.sqrt ‖radicalInner φ q q‖ := by
  rfl

end NormData

section HilbertInputs

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
variable [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
variable [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂]
variable [StarOrderedRing B₁ᵐᵒᵖ] [CompleteSpace E₁]
variable [StarOrderedRing B₂ᵐᵒᵖ] [CompleteSpace E₂]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. The radical tensor quotient is a right pre-Hilbert B₂-module with the descended inner
product and the square-root self-inner norm. -/
@[instance_reducible]
def radicalTensorCStarModule
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    letI : Norm (RadicalTensor (E₁ := E₁) φ) := radicalTensorNorm φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := by
  letI : Norm (RadicalTensor (E₁ := E₁) φ) := radicalTensorNorm φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  refine
    { inner := fun x y => MulOpposite.op (radicalInner φ x y)
      inner_add_right := ?_
      inner_self_nonneg := ?_
      inner_self := ?_
      inner_op_smul_right := ?_
      inner_smul_right_complex := ?_
      star_inner := ?_
      norm_eq_sqrt_norm_inner_self := ?_ }
  · intro x y z
    change MulOpposite.op (radicalInner φ x (y + z)) =
      MulOpposite.op (radicalInner φ x y) + MulOpposite.op (radicalInner φ x z)
    rw [map_add, MulOpposite.op_add]
  · intro x
    change 0 ≤ MulOpposite.op (radicalInner φ x x)
    obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective x
    simpa only [radicalInner_mkQ_mkQ] using balancedInner_self_nonneg φ z
  · intro x
    change MulOpposite.op (radicalInner φ x x) = 0 ↔ x = 0
    rw [MulOpposite.op_eq_zero_iff]
    exact radicalInner_self_eq_zero_iff φ x
  · intro a x y
    change MulOpposite.op (radicalInner φ x (radicalRightSMul φ a.unop y)) =
      a * MulOpposite.op (radicalInner φ x y)
    rw [radicalInner_radicalRightSMul, MulOpposite.op_mul, MulOpposite.op_unop]
  · intro c x y
    change MulOpposite.op (radicalInner φ x (c • y)) =
      c • MulOpposite.op (radicalInner φ x y)
    rw [map_smul, MulOpposite.op_smul]
  · intro x y
    change star (MulOpposite.op (radicalInner φ x y)) =
      MulOpposite.op (radicalInner φ y x)
    rw [← MulOpposite.op_star, star_radicalInner]
  · intro x
    change Real.sqrt ‖radicalInner φ x x‖ =
      Real.sqrt ‖MulOpposite.op (radicalInner φ x x)‖
    rw [MulOpposite.norm_op]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. The coefficient-valued inner product on the radical quotient is the descended tensor form,
viewed in B₂ᵐᵒᵖ. -/
@[simp]
theorem radicalTensorCStarModule_inner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x y : RadicalTensor (E₁ := E₁) φ) :
    letI : Norm (RadicalTensor (E₁ := E₁) φ) := radicalTensorNorm φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalTensorCStarModule φ;
    inner B₂ᵐᵒᵖ x y = MulOpposite.op (radicalInner φ x y) := by
  let : Norm (RadicalTensor (E₁ := E₁) φ) := radicalTensorNorm φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalTensorCStarModule φ
  rfl

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. The square-root self-inner norm satisfies the complex normed-space axioms on the radical
quotient. -/
theorem radicalTensor_normedSpaceCore
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    letI : Norm (RadicalTensor (E₁ := E₁) φ) := radicalTensorNorm φ;
    NormedSpace.Core ℂ (RadicalTensor (E₁ := E₁) φ) := by
  let : Norm (RadicalTensor (E₁ := E₁) φ) := radicalTensorNorm φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalTensorCStarModule φ
  exact CStarModule.normedSpaceCore B₂ᵐᵒᵖ (E := RadicalTensor (E₁ := E₁) φ)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. The radical tensor quotient is a normed additive group with the square-root self-inner
norm. -/
@[instance_reducible]
def radicalTensorNormedAddCommGroup
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := by
  letI : Norm (RadicalTensor (E₁ := E₁) φ) := radicalTensorNorm φ
  exact NormedAddCommGroup.ofCore (radicalTensor_normedSpaceCore φ)

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. The normed-group norm on the radical quotient equals the square-root self-inner norm. -/
theorem radicalTensorNormedAddCommGroup_norm
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (q : RadicalTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    ‖q‖ = Real.sqrt ‖radicalInner φ q q‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  rfl

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. The radical quotient is a complex normed space with that same square-root self-inner norm. -/
@[instance_reducible]
def radicalTensorNormedSpace
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  exact NormedSpace.ofCore (radicalTensor_normedSpaceCore φ)

end HilbertInputs

end CStarModule.InternalTensorProduct
