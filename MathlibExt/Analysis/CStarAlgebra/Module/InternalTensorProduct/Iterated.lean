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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapLeft.Functoriality

/-!
# Actual induced actions and right-associated completed internal tensors

Two original nonunital left actions define the right-associated interior
tensor using the existing literal balanced/radical/completion model. The
inner tensor's left action is computed by the already constructed completed
first-factor star homomorphism composed with the original coefficient map.

No norm, module, output IsModel, reassociation unitary or desired tensor
certificate is supplied. Coefficient algebras and the three original complete
fibres retain independent universes, their given opposite orders and actions.
Zero algebras/modules/actions are allowed; neither left action is assumed
faithful or nondegenerate. Full source associativity and the original Lance
Proposition4.5 balanced-null identity remain separate open proof boundaries.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uB₃ uE₁ uE₂ uE₃

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {B₃ : Type uB₃} [NonUnitalCStarAlgebra B₃]
  [PartialOrder B₃ᵐᵒᵖ] [StarOrderedRing B₃ᵐᵒᵖ]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {E₃ : Type uE₃} [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
  [SMul B₃ᵐᵒᵖ E₃] [CStarModule B₃ᵐᵒᵖ E₃] [CompleteSpace E₃]

/-- The original first coefficient acts on the actual inner completed tensor by the computed left functor. -/
def inducedCompletedLeftAction
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ (CompletedTensor (E₁ := E₂) χ) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  exact (completedLeftStarAlgHom (E₁ := E₂) χ).toNonUnitalStarAlgHom.comp φ

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ] in
/-- The induced coefficient value is the completed first-factor image. -/
theorem inducedCompletedLeftAction_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (b : B₁) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    inducedCompletedLeftAction φ χ b = completedLeftStarAlgHom χ (φ b) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  rfl

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ] in
/-- The induced action has its original first-factor value on a completed pure tensor. -/
@[simp]
theorem inducedCompletedLeftAction_completedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (b : B₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    inducedCompletedLeftAction φ χ b (completedPure χ y z) = completedPure χ (φ b y) z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  change completedLeftStarAlgHom χ (φ b) (completedPure χ y z) = completedPure χ (φ b y) z
  exact completedLeftStarAlgHom_pure χ (φ b) y z

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ] in
/-- The zero first coefficient homomorphism has the actual zero induced homomorphism. -/
@[simp]
theorem inducedCompletedLeftAction_zero
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    inducedCompletedLeftAction (0 : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) χ = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  apply NonUnitalStarAlgHom.ext
  intro b
  change completedLeftStarAlgHom χ (0 : AdjointableOperator.End B₂ E₂) = 0
  exact map_zero (completedLeftStarAlgHom χ)

variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]

/-- The literal completed tensor with the original inner tensor's computed first-coefficient action. -/
abbrev RightAssociatedCompletedTensor
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) : Type (max uE₁ uE₂ uE₃) :=
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  CompletedTensor (E₁ := E₁) (inducedCompletedLeftAction φ χ)

/-- The actual right-associated pure triple passes through both original tensor quotient/completion maps. -/
def rightAssociatedCompletedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃)
    (x : E₁) (y : E₂) (z : E₃) : RightAssociatedCompletedTensor (E₁ := E₁) φ χ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  exact completedPure η x (completedPure χ y z)

/-- The actual right-associated triple is the nested original completed pure map. -/
theorem rightAssociatedCompletedPure_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x y z = completedPure η x (completedPure χ y z) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  rfl

/-- The original left fibre is additive in the completed pure triple. -/
@[simp]
theorem rightAssociatedCompletedPure_add_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x x' : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ (x + x') y z =
      rightAssociatedCompletedPure φ χ x y z + rightAssociatedCompletedPure φ χ x' y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η (x + x') (completedPure χ y z) = completedPure η x (completedPure χ y z) +
    completedPure η x' (completedPure χ y z)
  exact completedPure_add_left η x x' (completedPure χ y z)

/-- The original middle fibre is additive in the completed pure triple. -/
@[simp]
theorem rightAssociatedCompletedPure_add_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y y' : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x (y + y') z =
      rightAssociatedCompletedPure φ χ x y z + rightAssociatedCompletedPure φ χ x y' z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ (y + y') z) = completedPure η x (completedPure χ y z) +
    completedPure η x (completedPure χ y' z)
  rw [completedPure_add_left χ]
  exact completedPure_add_right η x (completedPure χ y z) (completedPure χ y' z)

/-- The original right fibre is additive in the completed pure triple. -/
@[simp]
theorem rightAssociatedCompletedPure_add_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z z' : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x y (z + z') =
      rightAssociatedCompletedPure φ χ x y z + rightAssociatedCompletedPure φ χ x y z' := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ y (z + z')) = completedPure η x (completedPure χ y z) +
    completedPure η x (completedPure χ y z')
  rw [completedPure_add_right χ]
  exact completedPure_add_right η x (completedPure χ y z) (completedPure χ y z')

/-- Complex scaling in the original left fibre scales the same completed pure triple. -/
@[simp]
theorem rightAssociatedCompletedPure_smul_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ (c • x) y z = c • rightAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η (c • x) (completedPure χ y z) = c • completedPure η x (completedPure χ y z)
  exact completedPure_smul_left η c x (completedPure χ y z)

/-- Complex scaling in the original middle fibre scales the same completed pure triple. -/
@[simp]
theorem rightAssociatedCompletedPure_smul_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x (c • y) z = c • rightAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ (c • y) z) = c • completedPure η x (completedPure χ y z)
  rw [completedPure_smul_left χ]
  exact completedPure_smul_right η c x (completedPure χ y z)

/-- Complex scaling in the original right fibre scales the same completed pure triple. -/
@[simp]
theorem rightAssociatedCompletedPure_smul_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x y (c • z) = c • rightAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ y (c • z)) = c • completedPure η x (completedPure χ y z)
  rw [completedPure_smul_right χ]
  exact completedPure_smul_right η c x (completedPure χ y z)

/-- A zero left fibre vector has the actual zero completed pure value. -/
@[simp]
theorem rightAssociatedCompletedPure_zero_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ (0 : E₁) y z = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  simpa only [zero_smul] using
    rightAssociatedCompletedPure_smul_left φ χ (0 : ℂ) (0 : E₁) y z

/-- A zero middle fibre vector has the actual zero completed pure value. -/
@[simp]
theorem rightAssociatedCompletedPure_zero_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x (0 : E₂) z = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  simpa only [zero_smul] using
    rightAssociatedCompletedPure_smul_middle φ χ (0 : ℂ) x (0 : E₂) z

/-- A zero right fibre vector has the actual zero completed pure value. -/
@[simp]
theorem rightAssociatedCompletedPure_zero_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x y (0 : E₃) = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  simpa only [zero_smul] using
    rightAssociatedCompletedPure_smul_right φ χ (0 : ℂ) x y (0 : E₃)

/-- The first original coefficient balances through the given first left action. -/
@[simp]
theorem rightAssociatedCompletedPure_balance_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (b : B₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ (x <• b) y z = rightAssociatedCompletedPure φ χ x (φ b y) z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η (x <• b) (completedPure χ y z) =
    completedPure η x (completedPure χ (φ b y) z)
  rw [completedPure_balance]
  rw [inducedCompletedLeftAction_completedPure]

/-- The second original coefficient balances through the given second left action. -/
@[simp]
theorem rightAssociatedCompletedPure_balance_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (b : B₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    rightAssociatedCompletedPure φ χ x (y <• b) z = rightAssociatedCompletedPure φ χ x y (χ b z) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  change completedPure η x (completedPure χ (y <• b) z) =
    completedPure η x (completedPure χ y (χ b z))
  rw [completedPure_balance]

/-- The final original coefficient acts through the completed tensor right action. -/
@[simp]
theorem rightAssociatedCompletedPure_right_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z : E₃) (b : B₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ;
    letI : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ;
    let η := inducedCompletedLeftAction φ χ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₁) η) := radicalRightAction η;
    rightAssociatedCompletedPure φ χ x y (z <• b) = rightAssociatedCompletedPure φ χ x y z <• b := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₂) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₂) χ) := radicalRightAction χ
  let : CStarModule B₃ᵐᵒᵖ (CompletedTensor (E₁ := E₂) χ) := completedCStarModule χ
  let η := inducedCompletedLeftAction φ χ
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedAddCommGroup η
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) η) := radicalTensorNormedSpace η
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := E₁) η) := radicalRightAction η
  change completedPure η x (completedPure χ y (z <• b)) =
    completedPure η x (completedPure χ y z) <• b
  rw [completedPure_right_smul χ]
  exact completedPure_right_smul η x (completedPure χ y z) b

end CStarModule.InternalTensorProduct
