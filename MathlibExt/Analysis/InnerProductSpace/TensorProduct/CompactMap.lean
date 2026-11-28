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

public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.Compact
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.OperatorFaithfulness

/-!
# The algebraic tensor action of compact Hilbert-space maps

The tensor lift of compact factor maps takes values in the compact
operator submodule between the two Hilbert tensor completions. Its value
is the bounded completed tensor action, including finite sums and zero
factors. No norm on an algebraic tensor of compact operators is substituted.

Thus compact maps admit a compact-operator-valued algebraic tensor action.
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
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E₁`, `E₂`, `F₁`
and `F₂` be independent complete normed inner-product spaces over `𝕜`, possibly zero.
The actual algebraic tensor of compact maps from `E₁` to `E₂` and from `F₁` to `F₂`
acts linearly into the genuine compact-operator submodule between the two Hilbert tensor
completions, by the original completed tensor action on each pure operator tensor. -/
def compactMapLCompletionLinear :
    (compactOperator (RingHom.id 𝕜) E₁ E₂) ⊗[𝕜]
      (compactOperator (RingHom.id 𝕜) F₁ F₂) →ₗ[𝕜]
        compactOperator (RingHom.id 𝕜)
          (Completion (E₁ ⊗[𝕜] F₁)) (Completion (E₂ ⊗[𝕜] F₂)) := by
  let P₁ := compactOperator (RingHom.id 𝕜) E₁ E₂
  let P₂ := compactOperator (RingHom.id 𝕜) F₁ F₂
  let L : P₁ ⊗[𝕜] P₂ →ₗ[𝕜]
      Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) :=
    mapLCompletionLinear.comp (TensorProduct.map P₁.subtype P₂.subtype)
  have hL (z : P₁ ⊗[𝕜] P₂) : IsCompactOperator (L z) := by
    induction z using TensorProduct.inductionOn with
    | tmul f g =>
      change IsCompactOperator (mapLCompletion (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂))
      exact f.property.mapLCompletion g.property
    | add z w hz hw =>
      have hAdd : (L (z + w) :
          Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) = L z + L w :=
        map_add L z w
      have hCoe : ((L z + L w :
          Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
          Completion (E₁ ⊗[𝕜] F₁) → Completion (E₂ ⊗[𝕜] F₂)) =
          fun x => L z x + L w x := rfl
      rw [hAdd, hCoe]
      exact hz.add hw
  exact
    { toFun := fun z => ⟨L z, hL z⟩
      map_add' z w := Subtype.ext (map_add L z w)
      map_smul' c z := Subtype.ext (map_smul L c z) }

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E₁`, `E₂`, `F₁`
and `F₂` be independent complete normed inner-product spaces over `𝕜`, possibly zero.
For compact maps `f : E₁ →L[𝕜] E₂` and `g : F₁ →L[𝕜] F₂`, represented in their
actual compact submodules, the compact-valued algebraic tensor action has exactly the
bounded operator value `mapLCompletion f g` on `f ⊗ g`. -/
@[simp]
theorem compactMapLCompletionLinear_tmul
    (f : compactOperator (RingHom.id 𝕜) E₁ E₂)
    (g : compactOperator (RingHom.id 𝕜) F₁ F₂) :
    (compactMapLCompletionLinear (f ⊗ₜ[𝕜] g) :
      Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) =
        mapLCompletion (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) := rfl

end TensorProduct
