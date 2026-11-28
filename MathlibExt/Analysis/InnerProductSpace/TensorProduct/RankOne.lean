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
public import MathlibExt.Analysis.InnerProductSpace.CompactOperator.FiniteRankClosure
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Rank-one operators on the Hilbert tensor completion

Completed tensor products of rank-one operators are the rank-one operators
on the completed pure vectors. Their operator norms multiply, and their
completed action is compact. Scalars and all four factor spaces have
independent universes; factor completeness and nonzero vectors are not assumptions.

These finite-generator facts support the construction of compact tensor
operators.
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

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E₁`, `E₂`, `F₁`
and `F₂` be independent normed inner-product spaces, possibly zero. For vectors
`x₁ : E₁`, `x₂ : E₂`, `y₁ : F₁` and `y₂ : F₂`, the completed tensor action of the
two rank-one maps is exactly the rank-one operator from the completed pure input
vector `x₁ ⊗ y₁` to the completed pure output vector `x₂ ⊗ y₂`. -/
theorem mapLCompletion_rankOne (x₂ : E₂) (x₁ : E₁) (y₂ : F₂) (y₁ : F₁) :
    mapLCompletion (InnerProductSpace.rankOne 𝕜 x₂ x₁)
        (InnerProductSpace.rankOne 𝕜 y₂ y₁) =
      InnerProductSpace.rankOne 𝕜 (x₂ ⊗ₜ[𝕜] y₂ : Completion (E₂ ⊗[𝕜] F₂))
        (x₁ ⊗ₜ[𝕜] y₁ : Completion (E₁ ⊗[𝕜] F₁)) := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
    rw [mapLCompletion_tmul, InnerProductSpace.rankOne_apply,
      InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
      Completion.inner_coe, TensorProduct.inner_tmul,
      TensorProduct.smul_tmul_smul, Completion.coe_smul]
  | add u v hu hv =>
    simp only [Completion.coe_add, map_add, hu, hv]

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E₁`, `E₂`, `F₁`
and `F₂` be independent normed inner-product spaces, possibly zero. For arbitrary vectors
`x₁ : E₁`, `x₂ : E₂`, `y₁ : F₁` and `y₂ : F₂`, the operator norm of the completed
tensor action of the two rank-one maps is the product of their actual operator norms,
including the cases where a vector or factor space is zero. -/
theorem norm_mapLCompletion_rankOne (x₂ : E₂) (x₁ : E₁) (y₂ : F₂) (y₁ : F₁) :
    ‖mapLCompletion (InnerProductSpace.rankOne 𝕜 x₂ x₁)
        (InnerProductSpace.rankOne 𝕜 y₂ y₁)‖ =
      ‖InnerProductSpace.rankOne 𝕜 x₂ x₁‖ * ‖InnerProductSpace.rankOne 𝕜 y₂ y₁‖ := by
  rw [mapLCompletion_rankOne, InnerProductSpace.norm_rankOne,
    Completion.norm_coe, TensorProduct.norm_tmul,
    Completion.norm_coe, TensorProduct.norm_tmul,
    InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne]
  ring

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E₁`, `E₂`, `F₁`
and `F₂` be independent normed inner-product spaces, possibly zero. For arbitrary vectors
`x₁ : E₁`, `x₂ : E₂`, `y₁ : F₁` and `y₂ : F₂`, the actual completed tensor action
of the two rank-one maps is compact between the two Hilbert tensor completions. -/
theorem isCompactOperator_mapLCompletion_rankOne
    (x₂ : E₂) (x₁ : E₁) (y₂ : F₂) (y₁ : F₁) :
    IsCompactOperator (mapLCompletion (InnerProductSpace.rankOne 𝕜 x₂ x₁)
      (InnerProductSpace.rankOne 𝕜 y₂ y₁)) := by
  rw [mapLCompletion_rankOne]
  exact InnerProductSpace.finiteRankSubmodule_isCompactOperator
    (InnerProductSpace.rankOne_mem_finiteRankSubmodule _ _)

end TensorProduct
