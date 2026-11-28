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

import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CompactMap
import MathlibExt.Analysis.InnerProductSpace.TensorProduct.RankOne

/-!
# Public compact-tensor action computations

These clients use the stock Hilbert tensor completions over an arbitrary real or
complex scalar field, with all four factor spaces in independent universes. The
compact tensor action is tested on genuine rank-one compact maps, finite sums
acting on pure vectors, and an actual zero source factor. Completeness is used
where the compact tensor action requires it; the rank-one input bundling itself
requires no complete factor. All imports use the ordinary public API.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open UniformSpace
open scoped TensorProduct

namespace MathlibExtTest.CompactTensorPublicClient

universe u𝕜 uE₁ uE₂ uF₁ uF₂

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

private def rankOneCompact (x₂ : E₂) (x₁ : E₁) :
    compactOperator (RingHom.id 𝕜) E₁ E₂ :=
  ⟨InnerProductSpace.rankOne 𝕜 x₂ x₁,
    InnerProductSpace.finiteRankSubmodule_isCompactOperator
      (InnerProductSpace.rankOne_mem_finiteRankSubmodule x₂ x₁)⟩

variable [CompleteSpace E₁] [CompleteSpace E₂] [CompleteSpace F₁] [CompleteSpace F₂]

private theorem rankOne_tensor_action
    (x₂ : E₂) (x₁ : E₁) (y₂ : F₂) (y₁ : F₁) :
    (TensorProduct.compactMapLCompletionLinear
      (rankOneCompact (𝕜 := 𝕜) x₂ x₁ ⊗ₜ[𝕜] rankOneCompact (𝕜 := 𝕜) y₂ y₁) :
        Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) =
      InnerProductSpace.rankOne 𝕜
        (x₂ ⊗ₜ[𝕜] y₂ : Completion (E₂ ⊗[𝕜] F₂))
        (x₁ ⊗ₜ[𝕜] y₁ : Completion (E₁ ⊗[𝕜] F₁)) := by
  rw [TensorProduct.compactMapLCompletionLinear_tmul]
  change TensorProduct.mapLCompletion
    (InnerProductSpace.rankOne 𝕜 x₂ x₁) (InnerProductSpace.rankOne 𝕜 y₂ y₁) = _
  exact TensorProduct.mapLCompletion_rankOne x₂ x₁ y₂ y₁

private theorem sum_tensor_action
    (f₁ f₂ : compactOperator (RingHom.id 𝕜) E₁ E₂)
    (g₁ g₂ : compactOperator (RingHom.id 𝕜) F₁ F₂) (a : E₁) (b : F₁) :
    (TensorProduct.compactMapLCompletionLinear
      ((f₁ ⊗ₜ[𝕜] g₁) + (f₂ ⊗ₜ[𝕜] g₂)) :
        Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂))
          (a ⊗ₜ[𝕜] b : Completion (E₁ ⊗[𝕜] F₁)) =
      (((f₁ : E₁ →L[𝕜] E₂) a) ⊗ₜ[𝕜] ((g₁ : F₁ →L[𝕜] F₂) b) :
        Completion (E₂ ⊗[𝕜] F₂)) +
      (((f₂ : E₁ →L[𝕜] E₂) a) ⊗ₜ[𝕜] ((g₂ : F₁ →L[𝕜] F₂) b) :
        Completion (E₂ ⊗[𝕜] F₂)) := by
  rw [map_add]
  change
    ((TensorProduct.compactMapLCompletionLinear (f₁ ⊗ₜ[𝕜] g₁) :
        Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) +
      (TensorProduct.compactMapLCompletionLinear (f₂ ⊗ₜ[𝕜] g₂) :
        Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)))
          (a ⊗ₜ[𝕜] b : Completion (E₁ ⊗[𝕜] F₁)) = _
  rw [_root_.add_apply, TensorProduct.compactMapLCompletionLinear_tmul,
    TensorProduct.compactMapLCompletionLinear_tmul, TensorProduct.mapLCompletion_tmul,
    TensorProduct.mapLCompletion_tmul]

private theorem zero_left_tensor_action
    (g : compactOperator (RingHom.id 𝕜) F₁ F₂) :
    (TensorProduct.compactMapLCompletionLinear
      ((0 : compactOperator (RingHom.id 𝕜) E₁ E₂) ⊗ₜ[𝕜] g) :
        Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) = 0 := by
  rw [TensorProduct.zero_tmul, map_zero]
  rfl

private theorem zero_source_tensor_action [Subsingleton E₁]
    (f : compactOperator (RingHom.id 𝕜) E₁ E₂)
    (g : compactOperator (RingHom.id 𝕜) F₁ F₂) :
    (TensorProduct.compactMapLCompletionLinear (f ⊗ₜ[𝕜] g) :
      Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) = 0 := by
  have hf : f = 0 := by
    apply Subtype.ext
    ext a
    have ha : a = 0 := Subsingleton.elim a 0
    simp only [ha, map_zero]
  rw [hf]
  exact zero_left_tensor_action g

end MathlibExtTest.CompactTensorPublicClient
