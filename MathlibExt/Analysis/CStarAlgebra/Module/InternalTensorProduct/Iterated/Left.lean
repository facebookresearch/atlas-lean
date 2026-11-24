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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Iterated

/-!
# The actual left-associated completed internal tensor

The first literal completed tensor retains its existing norm, right action
and C-star module dictionaries. Applying the second original left action to
that original complete module gives the left-associated carrier and pure
triple. Both stages are the existing actual quotient/completion construction.

No output model, norm, completeness or associator certificate is an input.
All three coefficient and fibre universes, nonunital algebras, original
complete modules, given opposite orders and zero/degenerate actions remain.
Full source reassociation and the original Lance balanced-null identity are
separate whole-open theorem proof boundaries.
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
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {E₃ : Type uE₃} [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
  [SMul B₃ᵐᵒᵖ E₃] [CStarModule B₃ᵐᵒᵖ E₃] [CompleteSpace E₃]

/-- The literal left-associated completed tensor with both original coefficient actions. -/
abbrev LeftAssociatedCompletedTensor
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) : Type (max uE₁ uE₂ uE₃) :=
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  CompletedTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ

/-- The original left-associated triple uses the first completed pure tensor as the second tensor's first vector. -/
def leftAssociatedCompletedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃)
    (x : E₁) (y : E₂) (z : E₃) : LeftAssociatedCompletedTensor (E₁ := E₁) φ χ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  exact completedPure χ (completedPure φ x y) z

/-- The actual left-associated triple is the nested original completed pure map. -/
theorem leftAssociatedCompletedPure_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x y z = completedPure χ (completedPure φ x y) z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  rfl

/-- The original left fibre is additive in the completed pure triple. -/
@[simp]
theorem leftAssociatedCompletedPure_add_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x x' : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ (x + x') y z =
      leftAssociatedCompletedPure φ χ x y z + leftAssociatedCompletedPure φ χ x' y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ (x + x') y) z = completedPure χ (completedPure φ x y) z +
    completedPure χ (completedPure φ x' y) z
  rw [completedPure_add_left φ]
  exact completedPure_add_left χ (completedPure φ x y) (completedPure φ x' y) z

/-- The original middle fibre is additive in the completed pure triple. -/
@[simp]
theorem leftAssociatedCompletedPure_add_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y y' : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x (y + y') z =
      leftAssociatedCompletedPure φ χ x y z + leftAssociatedCompletedPure φ χ x y' z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x (y + y')) z = completedPure χ (completedPure φ x y) z +
    completedPure χ (completedPure φ x y') z
  rw [completedPure_add_right φ]
  exact completedPure_add_left χ (completedPure φ x y) (completedPure φ x y') z

/-- The original right fibre is additive in the completed pure triple. -/
@[simp]
theorem leftAssociatedCompletedPure_add_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z z' : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x y (z + z') =
      leftAssociatedCompletedPure φ χ x y z + leftAssociatedCompletedPure φ χ x y z' := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x y) (z + z') = completedPure χ (completedPure φ x y) z +
    completedPure χ (completedPure φ x y) z'
  exact completedPure_add_right χ (completedPure φ x y) z z'

/-- Complex scaling in the original left fibre scales the same completed pure triple. -/
@[simp]
theorem leftAssociatedCompletedPure_smul_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ (c • x) y z = c • leftAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ (c • x) y) z = c • completedPure χ (completedPure φ x y) z
  rw [completedPure_smul_left φ]
  exact completedPure_smul_left χ c (completedPure φ x y) z

/-- Complex scaling in the original middle fibre scales the same completed pure triple. -/
@[simp]
theorem leftAssociatedCompletedPure_smul_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x (c • y) z = c • leftAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x (c • y)) z = c • completedPure χ (completedPure φ x y) z
  rw [completedPure_smul_right φ]
  exact completedPure_smul_left χ c (completedPure φ x y) z

/-- Complex scaling in the original right fibre scales the same completed pure triple. -/
@[simp]
theorem leftAssociatedCompletedPure_smul_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (c : ℂ) (x : E₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x y (c • z) = c • leftAssociatedCompletedPure φ χ x y z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x y) (c • z) = c • completedPure χ (completedPure φ x y) z
  exact completedPure_smul_right χ c (completedPure φ x y) z

/-- A zero left fibre vector has the actual zero completed pure value. -/
@[simp]
theorem leftAssociatedCompletedPure_zero_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ (0 : E₁) y z = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  simpa only [zero_smul] using
    leftAssociatedCompletedPure_smul_left φ χ (0 : ℂ) (0 : E₁) y z

/-- A zero middle fibre vector has the actual zero completed pure value. -/
@[simp]
theorem leftAssociatedCompletedPure_zero_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x (0 : E₂) z = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  simpa only [zero_smul] using
    leftAssociatedCompletedPure_smul_middle φ χ (0 : ℂ) x (0 : E₂) z

/-- A zero right fibre vector has the actual zero completed pure value. -/
@[simp]
theorem leftAssociatedCompletedPure_zero_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x y (0 : E₃) = 0 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  simpa only [zero_smul] using
    leftAssociatedCompletedPure_smul_right φ χ (0 : ℂ) x y (0 : E₃)

/-- The first original coefficient balances through the given first left action. -/
@[simp]
theorem leftAssociatedCompletedPure_balance_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (b : B₁) (y : E₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ (x <• b) y z = leftAssociatedCompletedPure φ χ x (φ b y) z := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ (x <• b) y) z =
    completedPure χ (completedPure φ x (φ b y)) z
  rw [completedPure_balance]

/-- The second original coefficient balances through the given second left action. -/
@[simp]
theorem leftAssociatedCompletedPure_balance_middle
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (b : B₂) (z : E₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    leftAssociatedCompletedPure φ χ x (y <• b) z = leftAssociatedCompletedPure φ χ x y (χ b z) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  change completedPure χ (completedPure φ x (y <• b)) z =
    completedPure χ (completedPure φ x y) (χ b z)
  rw [completedPure_right_smul, completedPure_balance]

/-- The final original coefficient acts through the completed tensor right action. -/
@[simp]
theorem leftAssociatedCompletedPure_right_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (χ : B₂ →⋆ₙₐ[ℂ] AdjointableOperator.End B₃ E₃) (x : E₁) (y : E₂) (z : E₃) (b : B₃) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ;
    letI : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
      radicalRightAction χ;
    leftAssociatedCompletedPure φ χ x y (z <• b) = leftAssociatedCompletedPure φ χ x y z <• b := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let : NormedAddCommGroup (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalTensorNormedAddCommGroup χ
  let : NormedSpace ℂ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) := radicalTensorNormedSpace χ
  let : SMul B₃ᵐᵒᵖ (RadicalTensor (E₁ := CompletedTensor (E₁ := E₁) φ) χ) :=
    radicalRightAction χ
  change completedPure χ (completedPure φ x y) (z <• b) =
    completedPure χ (completedPure φ x y) z <• b
  exact completedPure_right_smul χ (completedPure φ x y) z b

end CStarModule.InternalTensorProduct
