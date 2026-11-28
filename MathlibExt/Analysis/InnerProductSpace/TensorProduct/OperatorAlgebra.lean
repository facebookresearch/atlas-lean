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

public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.OperatorFaithfulness
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.CompletionAdjoint
public import MathlibExt.Algebra.Star.StarAlgHom
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Star.TensorProduct

/-!
# Algebra and star laws for the completed tensor operator action

The algebraic tensor of bounded endomorphisms acts by a nonunital star
homomorphism on the Hilbert tensor completion. Multiplication and
involution follow from the pure operator values and tensor induction.
The action is defined on the algebraic tensor product of operator algebras
and takes values in operators on the Hilbert tensor completion.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open UniformSpace
open scoped TensorProduct

namespace TensorProduct

universe u𝕜 uH uK
variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [hK : CompleteSpace K]

omit hH hK in
/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`) and let `H` and `K` be independent
normed inner-product spaces over `𝕜`, including zero and incomplete factors. For all
algebraic tensors `z,w` of bounded endomorphisms of `H` and `K`, the actual completed
tensor operator action preserves multiplication on `Completion (H ⊗[𝕜] K)`. -/
theorem mapLCompletionLinear_mul
    (z w : (H →L[𝕜] H) ⊗[𝕜] (K →L[𝕜] K)) :
    mapLCompletionLinear (z * w) = mapLCompletionLinear z * mapLCompletionLinear w := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    induction w using TensorProduct.inductionOn with
    | tmul h k =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mapLCompletionLinear_tmul,
        mapLCompletionLinear_tmul, mapLCompletionLinear_tmul]
      exact mapLCompletion_mul f h g k
    | add w₁ w₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
  | add z₁ z₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, add_mul, h₁, h₂]

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`) and let `H` and `K` be
independent complete normed inner-product spaces over `𝕜`, possibly zero. For every
algebraic tensor `z` of bounded endomorphisms of the two spaces, the actual completed
tensor operator action sends its tensor involution to the operator adjoint involution. -/
theorem mapLCompletionLinear_star (z : (H →L[𝕜] H) ⊗[𝕜] (K →L[𝕜] K)) :
    mapLCompletionLinear (star z) = star (mapLCompletionLinear z) := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    rw [TensorProduct.star_tmul, mapLCompletionLinear_tmul, mapLCompletionLinear_tmul]
    exact (star_mapLCompletion f g).symm
  | add z w hz hw =>
    rw [star_add, map_add, map_add, star_add, hz, hw]

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`) and let `H` and `K` be
independent complete normed inner-product spaces over `𝕜`, possibly zero. The actual
algebraic tensor of their bounded endomorphisms acts on `Completion (H ⊗[𝕜] K)` by
this nonunital star-algebra homomorphism. Every value is the original completed tensor
operator; no tensor-completion norm or comparison is a premise. -/
def mapLCompletionNonUnitalStarAlgHom :
    (H →L[𝕜] H) ⊗[𝕜] (K →L[𝕜] K) →⋆ₙₐ[𝕜]
      (Completion (H ⊗[𝕜] K) →L[𝕜] Completion (H ⊗[𝕜] K)) :=
  NonUnitalStarAlgHom.ofLinearMap mapLCompletionLinear
    mapLCompletionLinear_mul mapLCompletionLinear_star

/-- Let `𝕜` be a real or complex scalar field (`RCLike 𝕜`) and let `H` and `K` be
independent complete normed inner-product spaces over `𝕜`, possibly zero. For bounded
endomorphisms `f` of `H` and `g` of `K`, the bundled algebraic star action has exactly
the original bounded completed tensor operator value `mapLCompletion f g` on `f ⊗ g`. -/
@[simp]
theorem mapLCompletionNonUnitalStarAlgHom_tmul (f : H →L[𝕜] H) (g : K →L[𝕜] K) :
    mapLCompletionNonUnitalStarAlgHom (f ⊗ₜ[𝕜] g) = mapLCompletion f g := rfl

end TensorProduct
