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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapRight.Bounded
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.OfPair

/-!
# Completed commuting right-factor operators

Let `E₁,E₂` be complete right C-star modules over nonunital `B₁,B₂` with star-compatible orders.
A complex nonunital star representation `φ : B₁ → End_(B₂)(E₂)` and an adjointable `S` commuting
with its image give the completed operator `I⊗S` on `E₁ ⊗_φ E₂`.

On pure tensors it sends `x⊗y` to `x⊗S y`, its adjoint sends them to `x⊗S* y`, and its norm is
at most `‖S‖`. These values extend the balanced and radical quotient maps through the norm
completion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]

/-- **Completed continuous right-factor map.** Let `E₁,E₂` be complete right C-star modules over
nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital star
representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`. extend the radical map
`I⊗S` to a continuous complex-linear endomorphism of the completed internal tensor. -/
def completedRightFactorCLM
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b)) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    CompletedTensor (E₁ := E₁) φ →L[ℂ] CompletedTensor (E₁ := E₁) φ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  exact ((UniformSpace.Completion.toComplL :
    RadicalTensor (E₁ := E₁) φ →L[ℂ] CompletedTensor (E₁ := E₁) φ).comp
      (radicalRightFactorCLM φ S hComm)).fromCompletion

/-- **Completed factor map on a radical image.** Let `E₁,E₂` be complete right C-star modules over
nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital star
representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`. for the completion
inclusion `j`, `completedRightFactorCLM φ S hComm (j q) = j (radicalRightFactorMap φ S hComm
q)`. -/
@[simp]
theorem completedRightFactorCLM_coe
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b))
    (q : RadicalTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    completedRightFactorCLM φ S hComm (q : CompletedTensor (E₁ := E₁) φ) =
      (radicalRightFactorMap φ S hComm q : CompletedTensor (E₁ := E₁) φ) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  simp only [completedRightFactorCLM, ContinuousLinearMap.fromCompletion_apply_coe,
    ContinuousLinearMap.comp_apply, UniformSpace.Completion.coe_toComplL,
    radicalRightFactorCLM_apply]

/-- **Completed factor map on balanced representatives.** Let `E₁,E₂` be complete right C-star
modules over nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex
nonunital star representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`. the
completed image of a balanced `z` is sent to the completed image of `balancedRightFactorMap φ
S hComm z`. -/
@[simp]
theorem completedRightFactorCLM_fromBalanced
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b))
    (z : BalancedTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    completedRightFactorCLM φ S hComm (completedFromBalanced φ z) =
      completedFromBalanced φ (balancedRightFactorMap φ S hComm z) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  rw [completedFromBalanced_apply, completedFromBalanced_apply,
    completedRightFactorCLM_coe, radicalRightFactorMap_mkQ]

/-- **Vector bound for the completed right factor.** Let `E₁,E₂` be complete right C-star modules
over nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital
star representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`.
`‖completedRightFactorCLM φ S hComm z‖ ≤ ‖S‖ * ‖z‖` for every completed tensor `z`. -/
theorem completedRightFactorCLM_norm_apply_le
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b))
    (z : CompletedTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    ‖completedRightFactorCLM φ S hComm z‖ ≤ ‖S‖ * ‖z‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  refine UniformSpace.Completion.induction_on z
    (isClosed_le (completedRightFactorCLM φ S hComm).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro q
  simpa only [completedRightFactorCLM_coe, UniformSpace.Completion.norm_coe] using
    radicalRightFactorMap_norm_le φ S hComm q

/-- **Completed right-factor adjoint pairing.** Let `E₁,E₂` be complete right C-star modules over
nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital star
representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`. the completed maps
satisfy `⟨(I⊗S)z,w⟩_(B₂) = ⟨z,(I⊗S*)w⟩_(B₂)`. -/
theorem completedRightFactorCLM_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b))
    (z w : CompletedTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    rightInner (B := B₂) (completedRightFactorCLM φ S hComm z) w =
      rightInner (B := B₂) z (completedRightFactorCLM φ S.adjointOperator
        (rightFactorCommutant_adjoint φ S hComm) w) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  have hl : Continuous fun p : CompletedTensor (E₁ := E₁) φ × CompletedTensor (E₁ := E₁) φ =>
      rightInner (B := B₂) (completedRightFactorCLM φ S hComm p.1) p.2 :=
    (CStarModule.continuous_rightInner (B := B₂) (E := CompletedTensor (E₁ := E₁) φ)).comp
      (((completedRightFactorCLM φ S hComm).continuous.comp continuous_fst).prodMk continuous_snd)
  have hr : Continuous fun p : CompletedTensor (E₁ := E₁) φ × CompletedTensor (E₁ := E₁) φ =>
      rightInner (B := B₂) p.1 (completedRightFactorCLM φ S.adjointOperator
        (rightFactorCommutant_adjoint φ S hComm) p.2) :=
    (CStarModule.continuous_rightInner (B := B₂) (E := CompletedTensor (E₁ := E₁) φ)).comp
      (continuous_fst.prodMk ((completedRightFactorCLM φ S.adjointOperator
        (rightFactorCommutant_adjoint φ S hComm)).continuous.comp continuous_snd))
  refine UniformSpace.Completion.induction_on₂ z w (isClosed_eq hl hr) ?_
  intro q v
  obtain ⟨q, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  obtain ⟨v, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective v
  have hq : ((radicalSpace (E₁ := E₁) φ).mkQ q : CompletedTensor (E₁ := E₁) φ) =
      completedFromBalanced φ q := (completedFromBalanced_apply φ q).symm
  have hv : ((radicalSpace (E₁ := E₁) φ).mkQ v : CompletedTensor (E₁ := E₁) φ) =
      completedFromBalanced φ v := (completedFromBalanced_apply φ v).symm
  rw [hq, hv, completedRightFactorCLM_fromBalanced, completedRightFactorCLM_fromBalanced,
    completedFromBalanced_inner, completedFromBalanced_inner]
  exact balancedRightFactorMap_inner_adjoint φ S hComm q v

/-- **Adjointable completed right factor.** Let `E₁,E₂` be complete right C-star modules over
nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital star
representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`. bundle `I⊗S` and its
adjoint `I⊗S*` as an adjointable endomorphism of the completed internal tensor. -/
def completedRightOperator
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b)) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    AdjointableOperator.End B₂ (CompletedTensor (E₁ := E₁) φ) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  exact AdjointableOperator.ofAdjointPair (completedRightFactorCLM φ S hComm)
    (completedRightFactorCLM φ S.adjointOperator (rightFactorCommutant_adjoint φ S hComm))
    (completedRightFactorCLM_inner_adjoint φ S hComm)

/-- **Completed right factor on a pure tensor.** Let `E₁,E₂` be complete right C-star modules over
nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital star
representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`.
`completedRightOperator φ S hComm (completedPure φ x y) = completedPure φ x (S y)`. -/
@[simp]
theorem completedRightOperator_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b))
    (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedRightOperator φ S hComm (completedPure φ x y) = completedPure φ x (S y) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  change completedRightFactorCLM φ S hComm (completedPure φ x y) = completedPure φ x (S y)
  rw [completedPure_apply, completedPure_apply, completedRightFactorCLM_coe,
    radicalRightFactorMap_pure]

/-- **Adjoint completed factor on a pure tensor.** Let `E₁,E₂` be complete right C-star modules
over nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital
star representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`. the adjoint of
`completedRightOperator φ S hComm` sends `completedPure φ x y` to `completedPure φ x
(S.adjoint y)`. -/
@[simp]
theorem completedRightOperator_adjoint_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b))
    (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    (completedRightOperator φ S hComm).adjoint (completedPure φ x y) =
      completedPure φ x (S.adjoint y) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  change completedRightFactorCLM φ S.adjointOperator (rightFactorCommutant_adjoint φ S hComm)
    (completedPure φ x y) = completedPure φ x (S.adjoint y)
  rw [completedPure_apply, completedPure_apply, completedRightFactorCLM_coe,
    radicalRightFactorMap_pure, AdjointableOperator.adjointOperator_apply]

/-- **Norm of the adjointable right factor.** Let `E₁,E₂` be complete right C-star modules over
nonunital `B₁,B₂` with star-compatible opposite orders, and let the complex nonunital star
representation `φ : B₁ → End_(B₂)(E₂)` commute with an adjointable `S`.
`‖completedRightOperator φ S hComm‖ ≤ ‖S‖`. -/
theorem completedRightOperator_norm_le
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂) (hComm : ∀ b : B₁, Commute S (φ b)) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    ‖completedRightOperator (E₁ := E₁) φ S hComm‖ ≤ ‖S‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  rw [AdjointableOperator.norm_eq]
  change ‖completedRightFactorCLM (E₁ := E₁) φ S hComm‖ ≤ ‖S‖
  exact ContinuousLinearMap.opNorm_le_bound _ (_root_.norm_nonneg S)
    (fun z => completedRightFactorCLM_norm_apply_le φ S hComm z)

end CStarModule.InternalTensorProduct
