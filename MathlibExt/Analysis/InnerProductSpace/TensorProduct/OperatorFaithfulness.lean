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
public import MathlibExt.LinearAlgebra.TensorProduct.HomInjective
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Faithfulness of the actual completed tensor operator action

The tensor lift of the bounded factor maps acts on the stock Hilbert tensor
completion. Its values on the actual raw core agree with the canonical
algebraic tensor action of the underlying linear maps. Raw faithfulness and
the genuine completion inclusion then prove injectivity, including zero
factor spaces. No norm comparison or completed-model certificate is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open UniformSpace
open scoped TensorProduct

namespace TensorProduct

universe u𝕜 uE₁ uE₂ uF₁ uF₂

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- The actual linear tensor lift of the bounded completed factor-map action. -/
noncomputable def mapLCompletionLinear :
    (E₁ →L[𝕜] E₂) ⊗[𝕜] (F₁ →L[𝕜] F₂) →ₗ[𝕜]
      Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) :=
  TensorProduct.lift
    { toFun := fun f =>
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
        exact mapLCompletion_smul_left c f g }

/-- A pure tensor of bounded operators has the original completed tensor action. -/
theorem mapLCompletionLinear_tmul (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    mapLCompletionLinear (f ⊗ₜ[𝕜] g) = mapLCompletion f g := rfl

/-- The actual completed action retains the canonical raw algebraic operator value. -/
theorem mapLCompletionLinear_coe
    (z : (E₁ →L[𝕜] E₂) ⊗[𝕜] (F₁ →L[𝕜] F₂)) (u : E₁ ⊗[𝕜] F₁) :
    mapLCompletionLinear z (u : Completion (E₁ ⊗[𝕜] F₁)) =
      (homTensorHomMap (RingHom.id 𝕜) E₁ F₁ E₂ F₂
        (TensorProduct.map (ContinuousLinearMap.coeLM 𝕜) (ContinuousLinearMap.coeLM 𝕜) z) u :
          Completion (E₂ ⊗[𝕜] F₂)) := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    simp only [mapLCompletionLinear_tmul, mapLCompletion_coe, map_tmul,
      homTensorHomMap_apply, mapL_apply, ContinuousLinearMap.coeLM_apply]
  | add z w hz hw =>
    simp only [map_add, _root_.add_apply, LinearMap.add_apply,
      Completion.coe_add, hz, hw]

/-- Finite tensors of bounded maps act faithfully on the original completed Hilbert tensor. -/
theorem mapLCompletionLinear_injective :
    Function.Injective
      (mapLCompletionLinear : (E₁ →L[𝕜] E₂) ⊗[𝕜] (F₁ →L[𝕜] F₂) →ₗ[𝕜]
        Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) := by
  classical
  let f : (E₁ →L[𝕜] E₂) →ₗ[𝕜] E₁ →ₗ[𝕜] E₂ := ContinuousLinearMap.coeLM 𝕜
  let g : (F₁ →L[𝕜] F₂) →ₗ[𝕜] F₁ →ₗ[𝕜] F₂ := ContinuousLinearMap.coeLM 𝕜
  have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr ContinuousLinearMap.coe_injective
  have hg : LinearMap.ker g = ⊥ := LinearMap.ker_eq_bot.mpr ContinuousLinearMap.coe_injective
  have hleft (z : (E₁ →L[𝕜] E₂) ⊗[𝕜] (F₁ →L[𝕜] F₂)) :
      TensorProduct.map f.leftInverse g.leftInverse (TensorProduct.map f g z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      rw [map_tmul, map_tmul, LinearMap.leftInverse_apply_of_inj hf,
        LinearMap.leftInverse_apply_of_inj hg]
    | add z w hz hw =>
      rw [map_add, map_add, hz, hw]
  have hmap : Function.Injective (TensorProduct.map f g) := by
    intro z w h
    have h' := congrArg (TensorProduct.map f.leftInverse g.leftInverse) h
    simpa only [hleft] using h'
  intro z w h
  apply hmap
  apply homTensorHomMap_injective
  apply LinearMap.ext
  intro u
  apply Completion.coe_injective
  have hcore := DFunLike.congr_fun h (u : Completion (E₁ ⊗[𝕜] F₁))
  simpa only [mapLCompletionLinear_coe] using hcore

end TensorProduct
