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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Completion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Coefficient-changing equivalences of completed internal tensors

The map is constructed on the actual balanced algebraic tensor, descended
through its radical quotient, and extended to the stock completion. Inner
covariance derives the right coefficient-action law. The source and target
coefficient and module universes are independent; no resulting tensor model,
inverse, norm equality, or radical-membership proof is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped CStarAlgebra RightActions TensorProduct BigOperators

namespace CStarModule.InternalTensorProduct

universe uB₁ uC₁ uB₂ uC₂ uE₁ uF₁ uE₂ uF₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {C₁ : Type uC₁} [NonUnitalCStarAlgebra C₁]
  [PartialOrder C₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {C₂ : Type uC₂} [NonUnitalCStarAlgebra C₂]
  [PartialOrder C₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]

variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [SMul C₁ᵐᵒᵖ F₁] [CStarModule C₁ᵐᵒᵖ F₁] [CompleteSpace F₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  [SMul C₂ᵐᵒᵖ F₂] [CStarModule C₂ᵐᵒᵖ F₂] [CompleteSpace F₂]

variable (φ : B₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End B₂ E₂)
variable (ψ : C₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End C₂ F₂)
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

private abbrev sourceRadicalNormedAddCommGroup :
    NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
  radicalTensorNormedAddCommGroup φ

attribute [local instance] sourceRadicalNormedAddCommGroup

private abbrev sourceRadicalNormedSpace :
    NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
  radicalTensorNormedSpace φ

attribute [local instance] sourceRadicalNormedSpace

private abbrev targetRadicalNormedAddCommGroup :
    NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
  radicalTensorNormedAddCommGroup ψ

attribute [local instance] targetRadicalNormedAddCommGroup

private abbrev targetRadicalNormedSpace :
    NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) :=
  radicalTensorNormedSpace ψ

attribute [local instance] targetRadicalNormedSpace

private abbrev sourceRadicalRightSMul :
    SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) :=
  radicalRightAction φ

attribute [local instance] sourceRadicalRightSMul

private abbrev targetRadicalRightSMul :
    SMul C₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) ψ) :=
  radicalRightAction ψ

attribute [local instance] targetRadicalRightSMul

private abbrev sourceRadicalCStarModule :
    CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) :=
  radicalTensorCStarModule φ

attribute [local instance] sourceRadicalCStarModule

private abbrev targetRadicalCStarModule :
    CStarModule C₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) ψ) :=
  radicalTensorCStarModule ψ

attribute [local instance] targetRadicalCStarModule

/-! ## Raw and balanced transport -/

private def rawTransport
    (L₁ : E₁ →ₗ[ℂ] F₁) (L₂ : E₂ →ₗ[ℂ] F₂) :
    AlgebraicTensor E₁ E₂ →ₗ[ℂ] AlgebraicTensor F₁ F₂ :=
  TensorProduct.map L₁ L₂

omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
@[simp]
private theorem rawTransport_tmul
    (L₁ : E₁ →ₗ[ℂ] F₁) (L₂ : E₂ →ₗ[ℂ] F₂)
    (x : E₁) (y : E₂) :
    rawTransport L₁ L₂ (x ⊗ₜ[ℂ] y) = L₁ x ⊗ₜ[ℂ] L₂ y := by
  simp only [rawTransport, TensorProduct.map_tmul]

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
  [PartialOrder C₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CStarModule B₁ᵐᵒᵖ E₁] [CStarModule C₁ᵐᵒᵖ F₁]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem balancingSpan_rawTransport
    (τ : B₁ → C₁)
    (L₁ : E₁ →ₗ[ℂ] F₁) (L₂ : E₂ →ₗ[ℂ] F₂)
    (hL₁ : ∀ (x : E₁) (b : B₁), L₁ (x <• b) = L₁ x <• τ b)
    (hL₂ : ∀ (b : B₁) (y : E₂),
      L₂ (φ b y) = ψ (τ b) (L₂ y)) :
    balancingSpan (E₁ := E₁) φ ≤
      (balancingSpan (E₁ := F₁) ψ).comap (rawTransport L₁ L₂) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨x, b, y⟩, rfl⟩
  change rawTransport L₁ L₂ (balanceRelation φ x b y) ∈
    balancingSpan (E₁ := F₁) ψ
  simp only [balanceRelation, map_sub, rawTransport_tmul, hL₁, hL₂]
  exact balanceRelation_mem ψ (L₁ x) (τ b) (L₂ y)

private def balancedTransport
    (τ : B₁ → C₁)
    (L₁ : E₁ →ₗ[ℂ] F₁) (L₂ : E₂ →ₗ[ℂ] F₂)
    (hL₁ : ∀ (x : E₁) (b : B₁), L₁ (x <• b) = L₁ x <• τ b)
    (hL₂ : ∀ (b : B₁) (y : E₂),
      L₂ (φ b y) = ψ (τ b) (L₂ y)) :
    BalancedTensor (E₁ := E₁) φ →ₗ[ℂ]
      BalancedTensor (E₁ := F₁) ψ :=
  (balancingSpan (E₁ := E₁) φ).mapQ
    (balancingSpan (E₁ := F₁) ψ) (rawTransport L₁ L₂)
    (balancingSpan_rawTransport φ ψ τ L₁ L₂ hL₁ hL₂)

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
  [PartialOrder C₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CStarModule B₁ᵐᵒᵖ E₁] [CStarModule C₁ᵐᵒᵖ F₁] in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem balancedTransport_mkQ
    (τ : B₁ → C₁)
    (L₁ : E₁ →ₗ[ℂ] F₁) (L₂ : E₂ →ₗ[ℂ] F₂)
    (hL₁ : ∀ (x : E₁) (b : B₁), L₁ (x <• b) = L₁ x <• τ b)
    (hL₂ : ∀ (b : B₁) (y : E₂),
      L₂ (φ b y) = ψ (τ b) (L₂ y))
    (z : AlgebraicTensor E₁ E₂) :
    balancedTransport φ ψ τ L₁ L₂ hL₁ hL₂
        ((balancingSpan (E₁ := E₁) φ).mkQ z) =
      (balancingSpan (E₁ := F₁) ψ).mkQ (rawTransport L₁ L₂ z) := by
  simp only [balancedTransport, Submodule.mkQ_apply, Submodule.mapQ_apply]

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
  [PartialOrder C₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CStarModule B₁ᵐᵒᵖ E₁] [CStarModule C₁ᵐᵒᵖ F₁]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
@[simp]
private theorem balancedTransport_pure
    (τ : B₁ → C₁)
    (L₁ : E₁ →ₗ[ℂ] F₁) (L₂ : E₂ →ₗ[ℂ] F₂)
    (hL₁ : ∀ (x : E₁) (b : B₁), L₁ (x <• b) = L₁ x <• τ b)
    (hL₂ : ∀ (b : B₁) (y : E₂),
      L₂ (φ b y) = ψ (τ b) (L₂ y))
    (x : E₁) (y : E₂) :
    balancedTransport φ ψ τ L₁ L₂ hL₁ hL₂ (balancedPure φ x y) =
      balancedPure ψ (L₁ x) (L₂ y) := by
  simp only [balancedPure, balancedTransport_mkQ, rawTransport_tmul]

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] in
include hinner₁ in
private theorem symm_right_smul (x : F₁) (c : C₁) :
    U₁.symm (x <• c) = U₁.symm x <• σ₁.symm c := by
  apply U₁.injective
  rw [U₁.apply_symm_apply,
    map_right_smul_of_map_rightInner σ₁ U₁ hinner₁,
    U₁.apply_symm_apply,
    σ₁.apply_symm_apply]

omit [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
  [PartialOrder C₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₂] [CompleteSpace F₂] in
include hφ in
private theorem symm_intertwines (c : C₁) (y : F₂) :
    U₂.symm (ψ c y) = φ (σ₁.symm c) (U₂.symm y) := by
  apply U₂.injective
  rw [U₂.apply_symm_apply, hφ, U₂.apply_symm_apply,
    σ₁.apply_symm_apply]

private def balancedForward :
    BalancedTensor (E₁ := E₁) φ →ₗ[ℂ]
      BalancedTensor (E₁ := F₁) ψ :=
  balancedTransport φ ψ σ₁ U₁.toLinearMap U₂.toLinearMap
    (map_right_smul_of_map_rightInner σ₁ U₁ hinner₁) hφ

include hinner₁ hφ in
private def balancedReverse :
    BalancedTensor (E₁ := F₁) ψ →ₗ[ℂ]
      BalancedTensor (E₁ := E₁) φ :=
  balancedTransport ψ φ σ₁.symm U₁.symm.toLinearMap U₂.symm.toLinearMap
    (symm_right_smul σ₁ U₁ hinner₁)
    (symm_intertwines φ ψ σ₁ U₂ hφ)

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem reverse_forward_pure (x : E₁) (y : E₂) :
    balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ
        (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ
          (balancedPure φ x y)) =
      balancedPure φ x y := by
  simp only [balancedForward, balancedReverse, balancedTransport_pure]
  change balancedPure φ (U₁.symm (U₁ x)) (U₂.symm (U₂ y)) =
    balancedPure φ x y
  rw [U₁.symm_apply_apply, U₂.symm_apply_apply]

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem forward_reverse_pure (x : F₁) (y : F₂) :
    balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ
        (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ
          (balancedPure ψ x y)) =
      balancedPure ψ x y := by
  simp only [balancedForward, balancedReverse, balancedTransport_pure]
  change balancedPure ψ (U₁ (U₁.symm x)) (U₂ (U₂.symm y)) =
    balancedPure ψ x y
  rw [U₁.apply_symm_apply, U₂.apply_symm_apply]

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem reverse_forward
    (q : BalancedTensor (E₁ := E₁) φ) :
    balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ
        (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ q) = q := by
  have hq : q ∈ Submodule.span ℂ
      (Set.range fun p : E₁ × E₂ => balancedPure φ p.1 p.2) := by
    rw [balancedPure_span_eq_top]
    trivial
  refine Submodule.span_induction
    (p := fun q _ => balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ
      (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ q) = q) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact reverse_forward_pure φ ψ σ₁ U₁ U₂ hinner₁ hφ x y
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · intro c x _ hx
    simpa only [map_smul] using congrArg (c • ·) hx

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem forward_reverse
    (q : BalancedTensor (E₁ := F₁) ψ) :
    balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ
        (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ q) = q := by
  have hq : q ∈ Submodule.span ℂ
      (Set.range fun p : F₁ × F₂ => balancedPure ψ p.1 p.2) := by
    rw [balancedPure_span_eq_top]
    trivial
  refine Submodule.span_induction
    (p := fun q _ => balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ
      (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ q) = q) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact forward_reverse_pure φ ψ σ₁ U₁ U₂ hinner₁ hφ x y
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · intro c x _ hx
    simpa only [map_smul] using congrArg (c • ·) hx

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ] in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem balancedForward_surjective :
    Function.Surjective (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ) := by
  intro q
  exact ⟨balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ q,
    forward_reverse φ ψ σ₁ U₁ U₂ hinner₁ hφ q⟩

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ] in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem balancedReverse_surjective :
    Function.Surjective (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ) := by
  intro q
  exact ⟨balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ q,
    reverse_forward φ ψ σ₁ U₁ U₂ hinner₁ hφ q⟩

/-! ## Inner covariance and radical descent -/

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
include hinner₁ hinner₂ hφ in
private theorem rawInner_forward
    (z w : AlgebraicTensor E₁ E₂) :
    rawInner ψ
        (rawTransport U₁.toLinearMap U₂.toLinearMap z)
        (rawTransport U₁.toLinearMap U₂.toLinearMap w) =
      σ₂ (rawInner φ z w) := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
      induction w using TensorProduct.inductionOn with
      | tmul y v =>
          rw [rawTransport_tmul, rawTransport_tmul,
            rawInner_tmul_tmul, rawInner_tmul_tmul]
          change CStarModule.rightInner (B := C₂) (U₂ u)
              (ψ (CStarModule.rightInner (B := C₁) (U₁ x) (U₁ y))
                (U₂ v)) =
            σ₂ (CStarModule.rightInner (B := B₂) u
              (φ (CStarModule.rightInner (B := B₁) x y) v))
          rw [hinner₁, ← hφ]
          exact hinner₂ u
            (φ (CStarModule.rightInner (B := B₁) x y) v)
      | add w w' hw hw' =>
          simp only [map_add, hw, hw']
  | add z z' hz hz' =>
      simp only [map_add, LinearMap.add_apply, hz, hz']

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
include hinner₁ hinner₂ hφ in
private theorem balancedInner_forward
    (q r : BalancedTensor (E₁ := E₁) φ) :
    balancedInner ψ
        (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ q)
        (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ r) =
      σ₂ (balancedInner φ q r) := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
  obtain ⟨w, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective r
  simp only [balancedForward, balancedTransport_mkQ,
    balancedInner_mkQ_mkQ]
  exact rawInner_forward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ z w

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ] in
include hinner₁ hinner₂ hφ in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem balancedInner_reverse
    (q r : BalancedTensor (E₁ := F₁) ψ) :
    balancedInner φ
        (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ q)
        (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ r) =
      σ₂.symm (balancedInner ψ q r) := by
  have h := balancedInner_forward
    φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
      (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ q)
      (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ r)
  rw [forward_reverse, forward_reverse] at h
  have h' := congrArg σ₂.symm h
  simpa only [σ₂.symm_apply_apply] using h'.symm

include hinner₁ hinner₂ hφ in
omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ] in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalSpace_forward :
    radicalSpace (E₁ := E₁) φ ≤
      (radicalSpace (E₁ := F₁) ψ).comap
        (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ) := by
  intro q hq
  apply (mem_radicalSpace_iff ψ
    (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ q)).2
  intro v
  obtain ⟨r, rfl⟩ :=
    balancedForward_surjective φ ψ σ₁ U₁ U₂ hinner₁ hφ v
  rw [balancedInner_forward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ q r,
    (mem_radicalSpace_iff φ q).1 hq r, map_zero]

include hinner₁ hinner₂ hφ in
omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ] in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalSpace_reverse :
    radicalSpace (E₁ := F₁) ψ ≤
      (radicalSpace (E₁ := E₁) φ).comap
        (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ) := by
  intro q hq
  apply (mem_radicalSpace_iff φ
    (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ q)).2
  intro v
  obtain ⟨r, rfl⟩ :=
    balancedReverse_surjective φ ψ σ₁ U₁ U₂ hinner₁ hφ v
  rw [balancedInner_reverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ q r,
    (mem_radicalSpace_iff ψ q).1 hq r, map_zero]

include hinner₁ hinner₂ hφ in
private def radicalForward :
    RadicalTensor (E₁ := E₁) φ →ₗ[ℂ]
      RadicalTensor (E₁ := F₁) ψ :=
  (radicalSpace (E₁ := E₁) φ).mapQ
    (radicalSpace (E₁ := F₁) ψ)
    (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ)
    (radicalSpace_forward
      φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)

include hinner₁ hinner₂ hφ in
private def radicalReverse :
    RadicalTensor (E₁ := F₁) ψ →ₗ[ℂ]
      RadicalTensor (E₁ := E₁) φ :=
  (radicalSpace (E₁ := F₁) ψ).mapQ
    (radicalSpace (E₁ := E₁) φ)
    (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ)
    (radicalSpace_reverse
      φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ] in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalForward_mkQ
    (q : BalancedTensor (E₁ := E₁) φ) :
    radicalForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        ((radicalSpace (E₁ := E₁) φ).mkQ q) =
      (radicalSpace (E₁ := F₁) ψ).mkQ
        (balancedForward φ ψ σ₁ U₁ U₂ hinner₁ hφ q) := by
  simp only [radicalForward, Submodule.mkQ_apply, Submodule.mapQ_apply]

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ] in
omit [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalReverse_mkQ
    (q : BalancedTensor (E₁ := F₁) ψ) :
    radicalReverse φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        ((radicalSpace (E₁ := F₁) ψ).mkQ q) =
      (radicalSpace (E₁ := E₁) φ).mkQ
        (balancedReverse φ ψ σ₁ U₁ U₂ hinner₁ hφ q) := by
  simp only [radicalReverse, Submodule.mkQ_apply, Submodule.mapQ_apply]

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalForward_pure (x : E₁) (y : E₂) :
    radicalForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        ((radicalSpace (E₁ := E₁) φ).mkQ (balancedPure φ x y)) =
      (radicalSpace (E₁ := F₁) ψ).mkQ
        (balancedPure ψ (U₁ x) (U₂ y)) := by
  rw [radicalForward_mkQ, balancedForward, balancedTransport_pure]
  change (radicalSpace (E₁ := F₁) ψ).mkQ
      (balancedPure ψ (U₁ x) (U₂ y)) =
    (radicalSpace (E₁ := F₁) ψ).mkQ
      (balancedPure ψ (U₁ x) (U₂ y))
  rfl

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalReverse_forward
    (q : RadicalTensor (E₁ := E₁) φ) :
    radicalReverse φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        (radicalForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ q) = q := by
  obtain ⟨q, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  simp only [radicalForward_mkQ, radicalReverse_mkQ, reverse_forward]

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalForward_reverse
    (q : RadicalTensor (E₁ := F₁) ψ) :
    radicalForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        (radicalReverse φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ q) = q := by
  obtain ⟨q, rfl⟩ := (radicalSpace (E₁ := F₁) ψ).mkQ_surjective q
  simp only [radicalReverse_mkQ, radicalForward_mkQ, forward_reverse]

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalInner_forward
    (q r : RadicalTensor (E₁ := E₁) φ) :
    radicalInner ψ
        (radicalForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ q)
        (radicalForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ r) =
      σ₂ (radicalInner φ q r) := by
  obtain ⟨q, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  obtain ⟨r, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective r
  simp only [radicalForward_mkQ, radicalInner_mkQ_mkQ]
  exact balancedInner_forward
    φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ q r

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
  [StarOrderedRing B₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace F₁] [CompleteSpace E₂] [CompleteSpace F₂] in
private theorem radicalInner_reverse
    (q r : RadicalTensor (E₁ := F₁) ψ) :
    radicalInner φ
        (radicalReverse φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ q)
        (radicalReverse φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ r) =
      σ₂.symm (radicalInner ψ q r) := by
  have h := radicalInner_forward
    φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
      (radicalReverse φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ q)
      (radicalReverse φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ r)
  rw [radicalForward_reverse, radicalForward_reverse] at h
  have h' := congrArg σ₂.symm h
  simpa only [σ₂.symm_apply_apply] using h'.symm

private theorem radicalRightInner_forward
    (q r : RadicalTensor (E₁ := E₁) φ) :
    CStarModule.rightInner (B := C₂)
        (radicalForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ q)
        (radicalForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ r) =
      σ₂ (CStarModule.rightInner (B := B₂) q r) := by
  change radicalInner ψ
      (radicalForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ q)
      (radicalForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ r) =
    σ₂ (radicalInner φ q r)
  exact radicalInner_forward φ ψ σ₁ σ₂ U₁ U₂
    hinner₁ hinner₂ hφ q r

private theorem radicalRightInner_reverse
    (q r : RadicalTensor (E₁ := F₁) ψ) :
    CStarModule.rightInner (B := B₂)
        (radicalReverse φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ q)
        (radicalReverse φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ r) =
      σ₂.symm (CStarModule.rightInner (B := C₂) q r) := by
  change radicalInner φ
      (radicalReverse φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ q)
      (radicalReverse φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ r) =
    σ₂.symm (radicalInner ψ q r)
  exact radicalInner_reverse φ ψ σ₁ σ₂ U₁ U₂
    hinner₁ hinner₂ hφ q r

/-! ## Actual normed equivalence -/

private theorem radicalForward_norm
    (q : RadicalTensor (E₁ := E₁) φ) :
    ‖radicalForward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ q‖ = ‖q‖ :=
  norm_map_of_map_rightInner σ₂
    (radicalForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)
    (fun b => StarAlgEquiv.norm_map σ₂ b)
    (radicalRightInner_forward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ) q

private theorem radicalReverse_norm
    (q : RadicalTensor (E₁ := F₁) ψ) :
    ‖radicalReverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ q‖ = ‖q‖ :=
  norm_map_of_map_rightInner σ₂.symm
    (radicalReverse φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)
    (fun c => StarAlgEquiv.norm_map σ₂.symm c)
    (radicalRightInner_reverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ) q

private def radicalForwardIsometry :
    RadicalTensor (E₁ := E₁) φ →ₗᵢ[ℂ]
      RadicalTensor (E₁ := F₁) ψ :=
  { toLinearMap :=
      radicalForward φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ
    norm_map' :=
      radicalForward_norm φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ }

private def radicalReverseIsometry :
    RadicalTensor (E₁ := F₁) ψ →ₗᵢ[ℂ]
      RadicalTensor (E₁ := E₁) φ :=
  { toLinearMap :=
      radicalReverse φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ
    norm_map' :=
      radicalReverse_norm φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ }


end CStarModule.InternalTensorProduct
namespace CStarModule.InternalTensorProduct

open Set
open CStarModule
open CStarModule.InternalTensorProduct
open scoped CStarAlgebra RightActions BigOperators

universe uB₁ uC₁ uB₂ uC₂ uE₁ uF₁ uE₂ uF₂ uI

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {C₁ : Type uC₁} [NonUnitalCStarAlgebra C₁]
  [PartialOrder C₁ᵐᵒᵖ] [StarOrderedRing C₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {C₂ : Type uC₂} [NonUnitalCStarAlgebra C₂]
  [PartialOrder C₂ᵐᵒᵖ] [StarOrderedRing C₂ᵐᵒᵖ]

variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [SMul C₁ᵐᵒᵖ F₁] [CStarModule C₁ᵐᵒᵖ F₁] [CompleteSpace F₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  [SMul C₂ᵐᵒᵖ F₂] [CStarModule C₂ᵐᵒᵖ F₂] [CompleteSpace F₂]

variable (φ : B₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End B₂ E₂)
variable (ψ : C₁ →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End C₂ F₂)
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

private abbrev completionSourceRadicalNormedAddCommGroup :
    NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
  radicalTensorNormedAddCommGroup φ

attribute [local instance] completionSourceRadicalNormedAddCommGroup

private abbrev completionSourceRadicalNormedSpace :
    NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
  radicalTensorNormedSpace φ

attribute [local instance] completionSourceRadicalNormedSpace

private abbrev completionTargetRadicalNormedAddCommGroup :
    NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
  radicalTensorNormedAddCommGroup ψ

attribute [local instance] completionTargetRadicalNormedAddCommGroup

private abbrev completionTargetRadicalNormedSpace :
    NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) :=
  radicalTensorNormedSpace ψ

attribute [local instance] completionTargetRadicalNormedSpace

private abbrev completionSourceRadicalRightSMul :
    SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) :=
  radicalRightAction φ

attribute [local instance] completionSourceRadicalRightSMul

private abbrev completionTargetRadicalRightSMul :
    SMul C₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) ψ) :=
  radicalRightAction ψ

attribute [local instance] completionTargetRadicalRightSMul

private abbrev completionSourceRadicalCStarModule :
    CStarModule B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) :=
  radicalTensorCStarModule φ

attribute [local instance] completionSourceRadicalCStarModule

private abbrev completionTargetRadicalCStarModule :
    CStarModule C₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) ψ) :=
  radicalTensorCStarModule ψ

attribute [local instance] completionTargetRadicalCStarModule

private abbrev completionSourceCStarModule :
    CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) :=
  completedCStarModule φ

attribute [local instance] completionSourceCStarModule

private abbrev completionTargetCStarModule :
    CStarModule C₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) ψ) :=
  completedCStarModule ψ

attribute [local instance] completionTargetCStarModule

/-! ## Extension of the constructed radical isometries -/

private def forwardIntoCompletion :
    RadicalTensor (E₁ := E₁) φ →ₗᵢ[ℂ]
      CompletedTensor (E₁ := F₁) ψ :=
  (UniformSpace.Completion.toComplₗᵢ :
    RadicalTensor (E₁ := F₁) ψ →ₗᵢ[ℂ]
      CompletedTensor (E₁ := F₁) ψ).comp
    (radicalForwardIsometry φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ)

private def reverseIntoCompletion :
    RadicalTensor (E₁ := F₁) ψ →ₗᵢ[ℂ]
      CompletedTensor (E₁ := E₁) φ :=
  (UniformSpace.Completion.toComplₗᵢ :
    RadicalTensor (E₁ := E₁) φ →ₗᵢ[ℂ]
      CompletedTensor (E₁ := E₁) φ).comp
    (radicalReverseIsometry φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ)

private def completedForward :
    CompletedTensor (E₁ := E₁) φ →ₗᵢ[ℂ]
      CompletedTensor (E₁ := F₁) ψ :=
  (forwardIntoCompletion φ ψ σ₁ σ₂ U₁ U₂
    hinner₁ hinner₂ hφ).fromCompletion

private def completedReverse :
    CompletedTensor (E₁ := F₁) ψ →ₗᵢ[ℂ]
      CompletedTensor (E₁ := E₁) φ :=
  (reverseIntoCompletion φ ψ σ₁ σ₂ U₁ U₂
    hinner₁ hinner₂ hφ).fromCompletion

private theorem completedForward_coe
    (q : RadicalTensor (E₁ := E₁) φ) :
    completedForward φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        (q : CompletedTensor (E₁ := E₁) φ) =
      (radicalForward φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ q :
          CompletedTensor (E₁ := F₁) ψ) := by
  rw [completedForward, LinearIsometry.fromCompletion_apply_coe]
  rfl

private theorem completedReverse_coe
    (q : RadicalTensor (E₁ := F₁) ψ) :
    completedReverse φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        (q : CompletedTensor (E₁ := F₁) ψ) =
      (radicalReverse φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ q :
          CompletedTensor (E₁ := E₁) φ) := by
  rw [completedReverse, LinearIsometry.fromCompletion_apply_coe]
  rfl

private theorem reverse_comp_forward :
    (completedReverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ).toContinuousLinearMap.comp
        (completedForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (CompletedTensor (E₁ := E₁) φ) := by
  apply ContinuousLinearMap.ext_on
    (UniformSpace.Completion.denseRange_coe.mono Submodule.subset_span)
  rintro _ ⟨q, rfl⟩
  change completedReverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ
        (completedForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ
            (q : CompletedTensor (E₁ := E₁) φ)) =
      (q : CompletedTensor (E₁ := E₁) φ)
  rw [completedForward_coe, completedReverse_coe]
  exact congrArg
    (fun r : RadicalTensor (E₁ := E₁) φ =>
      (r : CompletedTensor (E₁ := E₁) φ))
    (radicalReverse_forward
      φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ q)

private theorem forward_comp_reverse :
    (completedForward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ).toContinuousLinearMap.comp
        (completedReverse φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (CompletedTensor (E₁ := F₁) ψ) := by
  apply ContinuousLinearMap.ext_on
    (UniformSpace.Completion.denseRange_coe.mono Submodule.subset_span)
  rintro _ ⟨q, rfl⟩
  change completedForward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ
        (completedReverse φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ
            (q : CompletedTensor (E₁ := F₁) ψ)) =
      (q : CompletedTensor (E₁ := F₁) ψ)
  rw [completedReverse_coe, completedForward_coe]
  exact congrArg
    (fun r : RadicalTensor (E₁ := F₁) ψ =>
      (r : CompletedTensor (E₁ := F₁) ψ))
    (radicalForward_reverse
      φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ q)

private theorem forward_reverse_linear :
    (completedForward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ).toLinearMap.comp
        (completedReverse φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  change completedForward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ
        (completedReverse φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ z) = z
  have h := congrArg
    (fun L : CompletedTensor (E₁ := F₁) ψ →L[ℂ]
      CompletedTensor (E₁ := F₁) ψ => L z)
    (forward_comp_reverse
      φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)
  change completedForward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ
        (completedReverse φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ z) = z at h
  exact h

private theorem reverse_forward_linear :
    (completedReverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ).toLinearMap.comp
        (completedForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  change completedReverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ
        (completedForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ z) = z
  have h := congrArg
    (fun L : CompletedTensor (E₁ := E₁) φ →L[ℂ]
      CompletedTensor (E₁ := E₁) φ => L z)
    (reverse_comp_forward
      φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)
  change completedReverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ
        (completedForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ z) = z at h
  exact h

/-- Let B₁, B₂, C₁ and C₂ be possibly nonunital complex C-star algebras and E₁, E₂, F₁ and F₂
complete right Hilbert modules over their respective algebras. Let σ₁ and σ₂ be star algebra
equivalences of the corresponding coefficient algebras and U₁ and U₂ complex-linear
equivalences of the vector spaces that preserve the coefficient-valued inner products through
σ₁ and σ₂. Assume U₂ intertwines the two left coefficient representations through σ₁. Change
both coefficient algebras and tensor factors along inner-covariant complex linear equivalences
compatible with the left representations. The map and inverse are through balancing, the
radical and completion. -/
@[no_expose]
def completedSemilinearEquiv :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
      radicalTensorNormedAddCommGroup ψ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) := radicalTensorNormedSpace ψ;
    CompletedTensor (E₁ := E₁) φ ≃ₗᵢ[ℂ]
      CompletedTensor (E₁ := F₁) ψ :=
  LinearIsometryEquiv.ofLinearIsometry
    (completedForward φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ)
    (completedReverse φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ).toLinearMap
    (forward_reverse_linear
      φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)
    (reverse_forward_linear
      φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)

/-! ## Pure and finite-sum characteristics -/

/-- Let B₁, B₂, C₁ and C₂ be possibly nonunital complex C-star algebras and E₁, E₂, F₁ and F₂
complete right Hilbert modules over their respective algebras. Let σ₁ and σ₂ be star algebra
equivalences of the corresponding coefficient algebras and U₁ and U₂ complex-linear
equivalences of the vector spaces that preserve the coefficient-valued inner products through
σ₁ and σ₂. Assume U₂ intertwines the two left coefficient representations through σ₁. The
coefficient-changing equivalence sends a pure tensor to the tensor of the two transported
vectors. -/
@[simp]
theorem completedSemilinearEquiv_pure (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
      radicalTensorNormedAddCommGroup ψ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) := radicalTensorNormedSpace ψ;
    completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        (completedPure φ x y) =
      completedPure ψ (U₁ x) (U₂ y) := by
  change completedForward φ ψ σ₁ σ₂ U₁ U₂
    hinner₁ hinner₂ hφ (completedPure φ x y) = _
  rw [completedPure_apply, completedPure_apply,
    completedForward_coe, radicalForward_pure]

/-- Let B₁, B₂, C₁ and C₂ be possibly nonunital complex C-star algebras and E₁, E₂, F₁ and F₂
complete right Hilbert modules over their respective algebras. Let σ₁ and σ₂ be star algebra
equivalences of the corresponding coefficient algebras and U₁ and U₂ complex-linear
equivalences of the vector spaces that preserve the coefficient-valued inner products through
σ₁ and σ₂. Assume U₂ intertwines the two left coefficient representations through σ₁.
Transport computes termwise on a finite sum of pure tensors. -/
theorem completedSemilinearEquiv_sum_pure
    {I : Type uI} [Fintype I] (x : I → E₁) (y : I → E₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
      radicalTensorNormedAddCommGroup ψ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) := radicalTensorNormedSpace ψ;
    completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ
        (∑ i, completedPure φ (x i) (y i)) =
      ∑ i, completedPure ψ (U₁ (x i)) (U₂ (y i)) := by
  simp only [map_sum, completedSemilinearEquiv_pure]

/-! ## Completed coefficient-inner covariance -/

private theorem sourceCompletion_rightInner_coe
    (q r : RadicalTensor (E₁ := E₁) φ) :
    CStarModule.rightInner (B := B₂)
        (q : CompletedTensor (E₁ := E₁) φ)
        (r : CompletedTensor (E₁ := E₁) φ) =
      radicalInner φ q r := by
  change MulOpposite.unop
      (inner B₂ᵐᵒᵖ
        (q : CompletedTensor (E₁ := E₁) φ)
        (r : CompletedTensor (E₁ := E₁) φ)) = _
  rw [CStarModule.completionCStarModule_inner_coe_coe]
  simpa only [MulOpposite.unop_op] using congrArg MulOpposite.unop
    (radicalTensorCStarModule_inner φ q r)

private theorem targetCompletion_rightInner_coe
    (q r : RadicalTensor (E₁ := F₁) ψ) :
    CStarModule.rightInner (B := C₂)
        (q : CompletedTensor (E₁ := F₁) ψ)
        (r : CompletedTensor (E₁ := F₁) ψ) =
      radicalInner ψ q r := by
  change MulOpposite.unop
      (inner C₂ᵐᵒᵖ
        (q : CompletedTensor (E₁ := F₁) ψ)
        (r : CompletedTensor (E₁ := F₁) ψ)) = _
  rw [CStarModule.completionCStarModule_inner_coe_coe]
  simpa only [MulOpposite.unop_op] using congrArg MulOpposite.unop
    (radicalTensorCStarModule_inner ψ q r)

/-- Let B₁, B₂, C₁ and C₂ be possibly nonunital complex C-star algebras and E₁, E₂, F₁ and F₂
complete right Hilbert modules over their respective algebras. Let σ₁ and σ₂ be star algebra
equivalences of the corresponding coefficient algebras and U₁ and U₂ complex-linear
equivalences of the vector spaces that preserve the coefficient-valued inner products through
σ₁ and σ₂. Assume U₂ intertwines the two left coefficient representations through σ₁.
Transport intertwines the coefficient-valued inner product with the second coefficient-algebra
equivalence. -/
theorem completedSemilinearEquiv_rightInner
    (z w : CompletedTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
      radicalTensorNormedAddCommGroup ψ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) := radicalTensorNormedSpace ψ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : SMul C₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) ψ) := radicalRightAction ψ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : CStarModule C₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) ψ) := completedCStarModule ψ;
    CStarModule.rightInner (B := C₂)
        (completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ z)
        (completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ w) =
      σ₂ (CStarModule.rightInner (B := B₂) z w) := by
  change CStarModule.rightInner (B := C₂)
      (completedForward φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ z)
      (completedForward φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ w) =
    σ₂ (CStarModule.rightInner (B := B₂) z w)
  let P : CompletedTensor (E₁ := E₁) φ →
      CompletedTensor (E₁ := E₁) φ → Prop := fun z w =>
    CStarModule.rightInner (B := C₂)
        (completedForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ z)
        (completedForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ w) =
      σ₂ (CStarModule.rightInner (B := B₂) z w)
  change P z w
  refine UniformSpace.Completion.induction_on₂ (p := P) z w ?_ ?_
  · dsimp only [P]
    apply isClosed_eq
    · exact CStarModule.continuous_rightInner.comp
        (((completedForward φ ψ σ₁ σ₂ U₁ U₂
          hinner₁ hinner₂ hφ).continuous.comp continuous_fst).prodMk
          ((completedForward φ ψ σ₁ σ₂ U₁ U₂
            hinner₁ hinner₂ hφ).continuous.comp continuous_snd))
    · exact (map_continuous σ₂).comp CStarModule.continuous_rightInner
  · intro q r
    dsimp only [P]
    rw [completedForward_coe, completedForward_coe,
      targetCompletion_rightInner_coe,
      sourceCompletion_rightInner_coe,
      radicalInner_forward]

/-- Let B₁, B₂, C₁ and C₂ be possibly nonunital complex C-star algebras and E₁, E₂, F₁ and F₂
complete right Hilbert modules over their respective algebras. Let σ₁ and σ₂ be star algebra
equivalences of the corresponding coefficient algebras and U₁ and U₂ complex-linear
equivalences of the vector spaces that preserve the coefficient-valued inner products through
σ₁ and σ₂. Assume U₂ intertwines the two left coefficient representations through σ₁. The
induced equivalence of completed internal tensor products sends right multiplication by b in
B₂ to right multiplication by σ₂(b) in C₂. -/
theorem completedSemilinearEquiv_right_smul
    (z : CompletedTensor (E₁ := E₁) φ) (b : B₂) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    letI : NormedAddCommGroup (RadicalTensor (E₁ := F₁) ψ) :=
      radicalTensorNormedAddCommGroup ψ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := F₁) ψ) := radicalTensorNormedSpace ψ;
    letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
    letI : SMul C₂ᵐᵒᵖ (RadicalTensor (E₁ := F₁) ψ) := radicalRightAction ψ;
    letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    letI : CStarModule C₂ᵐᵒᵖ (CompletedTensor (E₁ := F₁) ψ) := completedCStarModule ψ;
    completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ (z <• b) =
      completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂
        hinner₁ hinner₂ hφ z <• σ₂ b :=
  map_right_smul_of_map_rightInner σ₂
    (completedSemilinearEquiv φ ψ σ₁ σ₂ U₁ U₂ hinner₁ hinner₂ hφ)
    (completedSemilinearEquiv_rightInner φ ψ σ₁ σ₂ U₁ U₂
      hinner₁ hinner₂ hφ) z b

end CStarModule.InternalTensorProduct
