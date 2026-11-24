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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.ModelComparison.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapRight.Completion

/-!
# Commuting right-factor operators on supplied internal-tensor models

Conjugate the computed canonical right-factor operator by the actual
canonical-to-model unitary. The model retains its original pure vectors,
coefficient actions, inner form and dense span. The descended operator uses
the caller's original opposite orders and independent carrier universes.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped RightActions
namespace CStarModule.InternalTensorProduct.IsModel

universe uB₁ uB₂ uE₁ uE₂ uX

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [SMul B₂ᵐᵒᵖ X] [CStarModule B₂ᵐᵒᵖ X] [CompleteSpace X]

/-- Descend a commuting right-factor operator to the same supplied complete tensor model. -/
@[no_expose]
def mapRightOperator
    {φ : B₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End B₂ E₂}
    {pure : E₁ → E₂ → X}
    (hX : CStarModule.InternalTensorProduct.IsModel φ pure)
    (S : CStarModule.AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    CStarModule.AdjointableOperator.End B₂ X := by
  letI : NormedAddCommGroup (CStarModule.InternalTensorProduct.RadicalTensor (E₁ := E₁) φ) :=
    CStarModule.InternalTensorProduct.radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (CStarModule.InternalTensorProduct.RadicalTensor (E₁ := E₁) φ) :=
    CStarModule.InternalTensorProduct.radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (CStarModule.InternalTensorProduct.RadicalTensor (E₁ := E₁) φ) :=
    CStarModule.InternalTensorProduct.radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CStarModule.InternalTensorProduct.CompletedTensor (E₁ := E₁) φ) :=
    CStarModule.InternalTensorProduct.completedCStarModule φ
  let U := CStarModule.InternalTensorProduct.completedTensorModelUnitary φ pure hX
  exact U.conjStarAlgHom
    (CStarModule.InternalTensorProduct.completedRightOperator (E₁ := E₁) φ S hComm)

/-- The descended right-factor operator has the original pure-model value. -/
@[simp]
theorem mapRightOperator_pure
    {φ : B₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End B₂ E₂}
    {pure : E₁ → E₂ → X}
    (hX : CStarModule.InternalTensorProduct.IsModel φ pure)
    (S : CStarModule.AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (x : E₁) (y : E₂) :
    mapRightOperator hX S hComm (pure x y) = pure x (S y) := by
  let : NormedAddCommGroup (CStarModule.InternalTensorProduct.RadicalTensor (E₁ := E₁) φ) :=
    CStarModule.InternalTensorProduct.radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (CStarModule.InternalTensorProduct.RadicalTensor (E₁ := E₁) φ) :=
    CStarModule.InternalTensorProduct.radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (CStarModule.InternalTensorProduct.RadicalTensor (E₁ := E₁) φ) :=
    CStarModule.InternalTensorProduct.radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CStarModule.InternalTensorProduct.CompletedTensor (E₁ := E₁) φ) :=
    CStarModule.InternalTensorProduct.completedCStarModule φ
  change (CStarModule.InternalTensorProduct.completedTensorModelUnitary φ pure hX).conjStarAlgHom
      (CStarModule.InternalTensorProduct.completedRightOperator (E₁ := E₁) φ S hComm)
      (pure x y) = pure x (S y)
  rw [CStarModule.UnitaryEquiv.conjStarAlgHom_apply,
    CStarModule.InternalTensorProduct.completedTensorModelUnitary_symm_pure,
    CStarModule.InternalTensorProduct.completedRightOperator_pure,
    CStarModule.InternalTensorProduct.completedTensorModelUnitary_pure]

end CStarModule.InternalTensorProduct.IsModel
