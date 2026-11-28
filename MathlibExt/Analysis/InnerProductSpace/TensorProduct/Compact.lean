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

public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.BilinearMap
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.RankOne

/-!
# Compact factors act compactly on the Hilbert tensor completion

The completed tensor action of two compact operators is compact. Its
operator-norm continuity allows rank-one approximation to be used
successively in the two factor-map spaces. The returned operator acts on
the inner-product tensor completions.

This supplies compactness for the compact-operator-valued algebraic tensor
action.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open UniformSpace Set
open scoped TensorProduct Topology

namespace TensorProduct

universe u𝕜 uE₁ uE₂ uF₁ uF₂
variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E₁`, `E₂`, `F₁`
and `F₂` be independent complete normed inner-product spaces over `𝕜`, possibly zero.
For compact bounded maps `f : E₁ →L[𝕜] E₂` and `g : F₁ →L[𝕜] F₂`, their actual
completed tensor action is compact from `Completion (E₁ ⊗[𝕜] F₁)` to
`Completion (E₂ ⊗[𝕜] F₂)`, with the original tensor inner-product norms. -/
theorem _root_.IsCompactOperator.mapLCompletion
    [CompleteSpace E₁] [CompleteSpace E₂] [CompleteSpace F₁] [CompleteSpace F₂]
    {f : E₁ →L[𝕜] E₂} {g : F₁ →L[𝕜] F₂}
    (hf : IsCompactOperator f) (hg : IsCompactOperator g) :
    IsCompactOperator (mapLCompletion f g) := by
  let Q := compactOperator (RingHom.id 𝕜)
    (Completion (E₁ ⊗[𝕜] F₁)) (Completion (E₂ ⊗[𝕜] F₂))
  let P₁ := InnerProductSpace.finiteRankSubmodule (𝕜 := 𝕜) (E := E₁) (F := E₂)
  let P₂ := InnerProductSpace.finiteRankSubmodule (𝕜 := 𝕜) (E := F₁) (F := F₂)
  have hRank (x : E₂) (y : E₁) :
      IsCompactOperator (mapLCompletionBilinear (InnerProductSpace.rankOne 𝕜 x y) g) := by
    let L : (F₁ →L[𝕜] F₂) →L[𝕜]
        Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) :=
      mapLCompletionContinuousBilinear
        (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂) (F₁ := F₁) (F₂ := F₂)
        (InnerProductSpace.rankOne 𝕜 x y)
    let J := Q.comap L.toLinearMap
    have hJ : IsClosed (J : Set (F₁ →L[𝕜] F₂)) :=
      isClosed_setOfPred_isCompactOperator.preimage L.continuous
    have hP : P₂ ≤ J := by
      apply Submodule.span_le.mpr
      rintro T ⟨⟨u, v⟩, rfl⟩
      change IsCompactOperator
        (TensorProduct.mapLCompletion (InnerProductSpace.rankOne 𝕜 x y)
          (InnerProductSpace.rankOne 𝕜 u v))
      exact isCompactOperator_mapLCompletion_rankOne x y u v
    have hgcl := hg.mem_topologicalClosure_finiteRankSubmodule
    change g ∈ closure (P₂ : Set (F₁ →L[𝕜] F₂)) at hgcl
    have hPset : (P₂ : Set (F₁ →L[𝕜] F₂)) ⊆ (J : Set (F₁ →L[𝕜] F₂)) := hP
    have hClosure : _root_.closure (P₂ : Set (F₁ →L[𝕜] F₂)) ⊆
        (J : Set (F₁ →L[𝕜] F₂)) := _root_.closure_minimal hPset hJ
    exact hClosure hgcl
  let L : (E₁ →L[𝕜] E₂) →L[𝕜]
      Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) :=
    (mapLCompletionContinuousBilinear
      (𝕜 := 𝕜) (E₁ := E₁) (E₂ := E₂) (F₁ := F₁) (F₂ := F₂)).flip g
  let J := Q.comap L.toLinearMap
  have hJ : IsClosed (J : Set (E₁ →L[𝕜] E₂)) :=
    isClosed_setOfPred_isCompactOperator.preimage L.continuous
  have hP : P₁ ≤ J := by
    apply Submodule.span_le.mpr
    rintro T ⟨⟨x, y⟩, rfl⟩
    exact hRank x y
  have hfcl := hf.mem_topologicalClosure_finiteRankSubmodule
  change f ∈ closure (P₁ : Set (E₁ →L[𝕜] E₂)) at hfcl
  have hPset : (P₁ : Set (E₁ →L[𝕜] E₂)) ⊆ (J : Set (E₁ →L[𝕜] E₂)) := hP
  have hClosure : _root_.closure (P₁ : Set (E₁ →L[𝕜] E₂)) ⊆
      (J : Set (E₁ →L[𝕜] E₂)) := _root_.closure_minimal hPset hJ
  exact hClosure hfcl

end TensorProduct
