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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Semilinear

/-!
# Functoriality of coefficient-changing completed tensor equivalences

Identity and composition are established on the dense span of actual pure
tensors. No extra action, inverse, or composite-compatibility premise is stored.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModule.InternalTensorProduct

open Set
open CStarModule
open CStarModule.InternalTensorProduct

universe uB₁ uC₁ uD₁ uB₂ uC₂ uD₂ uE₁ uF₁ uH₁ uE₂ uF₂ uH₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {C₁ : Type uC₁} [NonUnitalCStarAlgebra C₁]
  [PartialOrder C₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
variable {D₁ : Type uD₁} [NonUnitalCStarAlgebra D₁]
  [PartialOrder D₁ᵐᵒᵖ] [StarOrderedRing D₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {C₂ : Type uC₂} [NonUnitalCStarAlgebra C₂]
  [PartialOrder C₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
variable {D₂ : Type uD₂} [NonUnitalCStarAlgebra D₂]
  [PartialOrder D₂ᵐᵒᵖ] [StarOrderedRing D₂ᵐᵒᵖ]

variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [SMul C₁ᵐᵒᵖ F₁] [CStarModule C₁ᵐᵒᵖ F₁] [CompleteSpace F₁]
variable {H₁ : Type uH₁} [NormedAddCommGroup H₁] [NormedSpace ℂ H₁]
  [SMul D₁ᵐᵒᵖ H₁] [CStarModule D₁ᵐᵒᵖ H₁] [CompleteSpace H₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  [SMul C₂ᵐᵒᵖ F₂] [CStarModule C₂ᵐᵒᵖ F₂] [CompleteSpace F₂]
variable {H₂ : Type uH₂} [NormedAddCommGroup H₂] [NormedSpace ℂ H₂]
  [SMul D₂ᵐᵒᵖ H₂] [CStarModule D₂ᵐᵒᵖ H₂] [CompleteSpace H₂]

variable (φ : B₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End B₂ E₂)
variable (ψ : C₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End C₂ F₂)
variable (χ : D₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End D₂ H₂)

private abbrev coherenceSourceRadicalNormedAddCommGroup :
    NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
  radicalTensorNormedAddCommGroup φ

attribute [local instance] coherenceSourceRadicalNormedAddCommGroup

private abbrev coherenceSourceRadicalNormedSpace :
    NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
  radicalTensorNormedSpace φ

attribute [local instance] coherenceSourceRadicalNormedSpace

private abbrev coherenceMiddleRadicalNormedAddCommGroup :
    NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
  radicalTensorNormedAddCommGroup ψ

attribute [local instance] coherenceMiddleRadicalNormedAddCommGroup

private abbrev coherenceMiddleRadicalNormedSpace :
    NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) :=
  radicalTensorNormedSpace ψ

attribute [local instance] coherenceMiddleRadicalNormedSpace

private abbrev coherenceTargetRadicalNormedAddCommGroup :
    NormedAddCommGroup (RadicalTensor (E₁ := H₁) χ) :=
  radicalTensorNormedAddCommGroup χ

attribute [local instance] coherenceTargetRadicalNormedAddCommGroup

private abbrev coherenceTargetRadicalNormedSpace :
    NormedSpace ℂ (RadicalTensor (E₁ := H₁) χ) :=
  radicalTensorNormedSpace χ

attribute [local instance] coherenceTargetRadicalNormedSpace

/-! ## Identity coherence -/

/-- Identity coefficient and vector equivalences induce the identity on the
literal completed internal tensor. -/
theorem completedSemilinearEquiv_refl :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    completedSemilinearEquiv (φ := φ) (ψ := φ)
      (σ₁ := StarAlgEquiv.refl ℂ B₁) (σ₂ := StarAlgEquiv.refl ℂ B₂)
      (U₁ := LinearEquiv.refl ℂ E₁) (U₂ := LinearEquiv.refl ℂ E₂)
      (hinner₁ := fun _ _ ↦ rfl) (hinner₂ := fun _ _ ↦ rfl)
      (hφ := fun _ _ ↦ rfl) =
        LinearIsometryEquiv.refl ℂ (CompletedTensor (E₁ := E₁) φ) := by
  apply LinearIsometryEquiv.ext
  have hmaps :
      (completedSemilinearEquiv (φ := φ) (ψ := φ)
        (σ₁ := StarAlgEquiv.refl ℂ B₁) (σ₂ := StarAlgEquiv.refl ℂ B₂)
        (U₁ := LinearEquiv.refl ℂ E₁) (U₂ := LinearEquiv.refl ℂ E₂)
        (hinner₁ := fun _ _ ↦ rfl) (hinner₂ := fun _ _ ↦ rfl)
        (hφ := fun _ _ ↦ rfl)).toLinearIsometry.toContinuousLinearMap =
      (LinearIsometryEquiv.refl ℂ
        (CompletedTensor (E₁ := E₁) φ)).toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on (completedPure_dense_span φ)
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change completedSemilinearEquiv (φ := φ) (ψ := φ)
      (σ₁ := StarAlgEquiv.refl ℂ B₁) (σ₂ := StarAlgEquiv.refl ℂ B₂)
      (U₁ := LinearEquiv.refl ℂ E₁) (U₂ := LinearEquiv.refl ℂ E₂)
      (hinner₁ := fun _ _ ↦ rfl) (hinner₂ := fun _ _ ↦ rfl)
      (hφ := fun _ _ ↦ rfl) (completedPure φ x y) = completedPure φ x y
    exact completedSemilinearEquiv_pure
      (φ := φ) (ψ := φ)
      (σ₁ := StarAlgEquiv.refl ℂ B₁) (σ₂ := StarAlgEquiv.refl ℂ B₂)
      (U₁ := LinearEquiv.refl ℂ E₁) (U₂ := LinearEquiv.refl ℂ E₂)
      (hinner₁ := fun _ _ ↦ rfl) (hinner₂ := fun _ _ ↦ rfl)
      (hφ := fun _ _ ↦ rfl) x y
  intro z
  exact congrArg
    (fun L : CompletedTensor (E₁ := E₁) φ →L[ℂ]
      CompletedTensor (E₁ := E₁) φ ↦ L z) hmaps

/-! ## Two composable source-to-target diagrams -/

variable (σ₁ : B₁ ≃⋆ₐ[ℂ] C₁) (σ₂ : B₂ ≃⋆ₐ[ℂ] C₂)
variable (U₁ : E₁ ≃ₗ[ℂ] F₁) (U₂ : E₂ ≃ₗ[ℂ] F₂)
variable (hinner₁ : ∀ x y : E₁,
  CStarModule.rightInner (B := C₁) (U₁ x) (U₁ y) =
    σ₁ (CStarModule.rightInner (B := B₁) x y))
variable (hinner₂ : ∀ x y : E₂,
  CStarModule.rightInner (B := C₂) (U₂ x) (U₂ y) =
    σ₂ (CStarModule.rightInner (B := B₂) x y))
variable (hφ : ∀ (b : B₁) (y : E₂),
  U₂ (φ b y) = ψ (σ₁ b) (U₂ y))

variable (τ₁ : C₁ ≃⋆ₐ[ℂ] D₁) (τ₂ : C₂ ≃⋆ₐ[ℂ] D₂)
variable (V₁ : F₁ ≃ₗ[ℂ] H₁) (V₂ : F₂ ≃ₗ[ℂ] H₂)
variable (kinner₁ : ∀ x y : F₁,
  CStarModule.rightInner (B := D₁) (V₁ x) (V₁ y) =
    τ₁ (CStarModule.rightInner (B := C₁) x y))
variable (kinner₂ : ∀ x y : F₂,
  CStarModule.rightInner (B := D₂) (V₂ x) (V₂ y) =
    τ₂ (CStarModule.rightInner (B := C₂) x y))
variable (kφ : ∀ (c : C₁) (y : F₂),
  V₂ (ψ c y) = χ (τ₁ c) (V₂ y))

/-- The constructed coefficient-changing tensor equivalence respects
composition of compatible diagrams. Composite inner laws and the
representation square are derived, not supplied as additional premises. -/
theorem completedSemilinearEquiv_trans :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
      radicalTensorNormedAddCommGroup ψ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) := radicalTensorNormedSpace ψ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := H₁) χ) :=
      radicalTensorNormedAddCommGroup χ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := H₁) χ) := radicalTensorNormedSpace χ;
    let hcomp₁ : ∀ x y : E₁,
        rightInner (B := D₁) ((U₁.trans V₁) x) ((U₁.trans V₁) y) =
          (σ₁.trans τ₁) (rightInner (B := B₁) x y) := fun x y ↦ by
            change rightInner (B := D₁) (V₁ (U₁ x)) (V₁ (U₁ y)) =
              τ₁ (σ₁ (rightInner (B := B₁) x y))
            rw [kinner₁, hinner₁]
    let hcomp₂ : ∀ x y : E₂,
        rightInner (B := D₂) ((U₂.trans V₂) x) ((U₂.trans V₂) y) =
          (σ₂.trans τ₂) (rightInner (B := B₂) x y) := fun x y ↦ by
            change rightInner (B := D₂) (V₂ (U₂ x)) (V₂ (U₂ y)) =
              τ₂ (σ₂ (rightInner (B := B₂) x y))
            rw [kinner₂, hinner₂]
    let hcompφ : ∀ (b : B₁) (y : E₂),
        (U₂.trans V₂) (φ b y) =
          χ ((σ₁.trans τ₁) b) ((U₂.trans V₂) y) := fun b y ↦ by
            change V₂ (U₂ (φ b y)) = χ (τ₁ (σ₁ b)) (V₂ (U₂ y))
            rw [hφ, kφ]
    completedSemilinearEquiv φ χ (σ₁.trans τ₁) (σ₂.trans τ₂)
        (U₁.trans V₁) (U₂.trans V₂) hcomp₁ hcomp₂ hcompφ =
      (completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ).trans
        (completedSemilinearEquiv ψ χ τ₁ τ₂ V₁ V₂
          kinner₁ kinner₂ kφ) := by
  dsimp only
  let hcomp₁ : ∀ x y : E₁,
      rightInner (B := D₁) ((U₁.trans V₁) x) ((U₁.trans V₁) y) =
        (σ₁.trans τ₁) (rightInner (B := B₁) x y) := fun x y ↦ by
    change rightInner (B := D₁) (V₁ (U₁ x)) (V₁ (U₁ y)) =
      τ₁ (σ₁ (rightInner (B := B₁) x y))
    rw [kinner₁, hinner₁]
  let hcomp₂ : ∀ x y : E₂,
      rightInner (B := D₂) ((U₂.trans V₂) x) ((U₂.trans V₂) y) =
        (σ₂.trans τ₂) (rightInner (B := B₂) x y) := fun x y ↦ by
    change rightInner (B := D₂) (V₂ (U₂ x)) (V₂ (U₂ y)) =
      τ₂ (σ₂ (rightInner (B := B₂) x y))
    rw [kinner₂, hinner₂]
  let hcompφ : ∀ (b : B₁) (y : E₂),
      (U₂.trans V₂) (φ b y) = χ ((σ₁.trans τ₁) b) ((U₂.trans V₂) y) :=
    fun b y ↦ by
      change V₂ (U₂ (φ b y)) = χ (τ₁ (σ₁ b)) (V₂ (U₂ y))
      rw [hφ, kφ]
  apply LinearIsometryEquiv.ext
  have hmaps :
      (completedSemilinearEquiv φ χ (σ₁.trans τ₁) (σ₂.trans τ₂)
        (U₁.trans V₁) (U₂.trans V₂)
        hcomp₁ hcomp₂ hcompφ).toLinearIsometry.toContinuousLinearMap =
      ((completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ).trans
        (completedSemilinearEquiv ψ χ τ₁ τ₂ V₁ V₂
          kinner₁ kinner₂ kφ)).toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on (completedPure_dense_span φ)
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change completedSemilinearEquiv φ χ (σ₁.trans τ₁) (σ₂.trans τ₂)
        (U₁.trans V₁) (U₂.trans V₂) hcomp₁ hcomp₂ hcompφ (completedPure φ x y) =
      completedSemilinearEquiv ψ χ τ₁ τ₂ V₁ V₂ kinner₁ kinner₂ kφ
        (completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ (completedPure φ x y))
    rw [completedSemilinearEquiv_pure, completedSemilinearEquiv_pure,
      completedSemilinearEquiv_pure]
    rfl
  intro z
  exact congrArg
    (fun L : CompletedTensor (E₁ := E₁) φ →L[ℂ]
      CompletedTensor (E₁ := H₁) χ ↦ L z) hmaps

end CStarModule.InternalTensorProduct
