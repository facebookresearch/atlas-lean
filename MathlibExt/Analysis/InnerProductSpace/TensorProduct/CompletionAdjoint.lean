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

public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CompletionMap

/-!
# Adjoints of maps on completed Hilbert tensors

The adjoint identity is proved using the original algebraic tensor inner
product and its dense image in the stock completion. Factor Hilbert spaces
are complete; the algebraic tensor has no completeness hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open UniformSpace
open scoped TensorProduct

namespace TensorProduct

universe u𝕜 uE₁ uE₂ uF₁ uF₂

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
variable [CompleteSpace E₁] [CompleteSpace E₂]
variable [CompleteSpace F₁] [CompleteSpace F₂]

/-- The actual Hilbert-space adjoint on the completed tensor is the tensor
map of the factor adjoints. -/
@[simp]
theorem adjoint_mapLCompletion (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    (mapLCompletion f g).adjoint = mapLCompletion f.adjoint g.adjoint := by
  have hAlg (v : E₂ ⊗[𝕜] F₂) (u : E₁ ⊗[𝕜] F₁) :
      inner 𝕜 (mapL f.adjoint g.adjoint v) u = inner 𝕜 v (mapL f g u) := by
    refine v.inductionOn ?_ ?_
    · intro vE vF
      refine u.inductionOn ?_ ?_
      · intro uE uF
        simp only [mapL_tmul, inner_tmul, ContinuousLinearMap.adjoint_inner_left]
      · intro u₁ u₂ h₁ h₂
        simp only [map_add, inner_add_right, h₁, h₂]
    · intro v₁ v₂ h₁ h₂
      simp only [map_add, inner_add_left, h₁, h₂]
  apply Eq.symm
  refine (ContinuousLinearMap.eq_adjoint_iff
    (mapLCompletion f.adjoint g.adjoint) (mapLCompletion f g)).2 ?_
  intro v u
  refine Completion.induction_on₂ v u (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro v₀ u₀
  simpa only [mapLCompletion_coe, Completion.inner_coe] using hAlg v₀ u₀

/-- For factor endomorphisms, the completed map preserves the operator star. -/
@[simp]
theorem star_mapLCompletion (f : E₁ →L[𝕜] E₁) (g : F₁ →L[𝕜] F₁) :
    star (mapLCompletion f g) = mapLCompletion (star f) (star g) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using adjoint_mapLCompletion f g

end TensorProduct
