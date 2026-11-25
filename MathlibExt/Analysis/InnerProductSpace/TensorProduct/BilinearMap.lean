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
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The continuous bilinear completed tensor-operator action

The completed tensor action is jointly continuous in the two operator
norms. This packages its linearity in both factor maps and the product
bound. The scalar field and all four inner-product-space universes are
independent; zero and incomplete factor spaces are included.

Operator-norm continuity supports norm-closure arguments for compact
factor maps.
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
and `F₂` be independent normed inner-product spaces over `𝕜`, possibly zero. The actual
completed tensor action `mapLCompletion f g` of bounded maps `f : E₁ →L[𝕜] E₂` and
`g : F₁ →L[𝕜] F₂` is linear in each factor map, as the following bilinear map. -/
def mapLCompletionBilinear :
    (E₁ →L[𝕜] E₂) →ₗ[𝕜] (F₁ →L[𝕜] F₂) →ₗ[𝕜]
      Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) where
  toFun f :=
    { toFun := fun g => mapLCompletion f g
      map_add' g h := mapLCompletion_add_right f g h
      map_smul' c g := mapLCompletion_smul_right c f g }
  map_add' f h := by
    apply LinearMap.ext
    intro g
    exact mapLCompletion_add_left f h g
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    exact mapLCompletion_smul_left c f g

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E₁`, `E₂`, `F₁`
and `F₂` be independent normed inner-product spaces over `𝕜`, possibly zero. With the
actual operator norms on the two bounded-map spaces, their completed tensor action is
jointly continuous: `‖mapLCompletion f g‖ ≤ ‖f‖ * ‖g‖`. This is that same bilinear
map bundled as a continuous linear map with continuous-linear-map values. -/
def mapLCompletionContinuousBilinear :
    (E₁ →L[𝕜] E₂) →L[𝕜] (F₁ →L[𝕜] F₂) →L[𝕜]
      Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) :=
  mapLCompletionBilinear.mkContinuous₂ 1 (by
    intro f g
    simp only [one_mul]
    change ‖mapLCompletion f g‖ ≤ ‖f‖ * ‖g‖
    exact norm_mapLCompletion_le f g)

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`), and let `E₁`, `E₂`, `F₁`
and `F₂` be independent normed inner-product spaces over `𝕜`, possibly zero. For every
bounded `f : E₁ →L[𝕜] E₂` and `g : F₁ →L[𝕜] F₂`, the continuous bilinear object
has exactly the original completed tensor-operator value `mapLCompletion f g`. -/
@[simp]
theorem mapLCompletionContinuousBilinear_apply (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    mapLCompletionContinuousBilinear f g = mapLCompletion f g := rfl

end TensorProduct
