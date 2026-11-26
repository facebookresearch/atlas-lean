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
# Commuting factors on internal tensor presentations

Let `E₁,E₂` be complete right modules over nonunital C-star algebras `B₁,B₂` with
star-compatible opposite orders, and let `φ : B₁ → End_(B₂)(E₂)` be a complex nonunital star
homomorphism. Let `X` be a complete right `B₂`-module with a pure map `p : E₁ × E₂ → X`
satisfying the balanced inner-product and dense-span conditions for `E₁ ⊗_φ E₂`. The comparison
unitary `U` is characterized by `U(completedPure φ x y) = p(x,y)`.

For an adjointable `S` on `E₂` commuting with the star representation `φ : B₁ → End_(B₂)(E₂)`,
conjugate the completed operator `I⊗S` through `U`. The resulting adjointable operator on `X` is
determined by `p(x,y) ↦ p(x,S y)`. The coefficient algebras are nonunital, their opposite orders
star-compatible, and the component modules complete.
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

/-- **Right factor on a complete tensor presentation.** Let `E₁,E₂` be complete right C-star
modules over nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex
nonunital star representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`. if
`X,p` satisfy `IsModel φ p`, the comparison unitary `U` gives `U (I⊗S) U*` on `X`,
characterized by `p(x,y) ↦ p(x,S y)`. -/
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

/-- **Right factor on pure presentation vectors.** Let `E₁,E₂` be complete right C-star modules
over nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital
star representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`. for a complete
presentation `X,p` with `hX : IsModel φ p`, `mapRightOperator hX S hComm (p x y) = p x (S y)`. -/
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
