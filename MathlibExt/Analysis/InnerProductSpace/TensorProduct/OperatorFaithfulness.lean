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
public import MathlibExt.LinearAlgebra.TensorProduct.HomInjective
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Faithfulness of finite tensors of bounded operators

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜 in independent universes, and
write E⊗̂F for the completion of the inner-product tensor norm. For bounded linear f:E₁→E₂ and
g:F₁→F₂, the operator f⊗̂g sends completed pure tensors x⊗y to f(x)⊗g(y). Let Φ be the
𝕜-linear map from (E₁→L[𝕜]E₂)⊗(F₁→L[𝕜]F₂) to bounded maps E₁⊗̂F₁→E₂⊗̂F₂, with Φ(f⊗g)=f⊗̂g. The
map Φ=mapLCompletionLinear is injective, so a finite algebraic tensor of bounded maps is
determined by its action on the Hilbert tensor completion. Zero and incomplete factor spaces
are included.
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

/-- **Linear tensor action of bounded factor maps.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜 in independent universes, and
write E⊗̂F for the completion of the inner-product tensor norm. For bounded linear f:E₁→E₂ and
g:F₁→F₂, the operator f⊗̂g sends completed pure tensors x⊗y to f(x)⊗g(y). Let Φ be the
𝕜-linear map from (E₁→L[𝕜]E₂)⊗(F₁→L[𝕜]F₂) to bounded maps E₁⊗̂F₁→E₂⊗̂F₂, with Φ(f⊗g)=f⊗̂g. The
map mapLCompletionLinear is Φ on the algebraic tensor of the bounded-map spaces.
-/
noncomputable def mapLCompletionLinear :
    (E₁ →L[𝕜] E₂) ⊗[𝕜] (F₁ →L[𝕜] F₂) →ₗ[𝕜]
      Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) :=
  TensorProduct.lift mapLCompletionBilinear

/-- **Pure operator tensor acts as the completed tensor map.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜 in independent universes, and
write E⊗̂F for the completion of the inner-product tensor norm. For bounded linear f:E₁→E₂ and
g:F₁→F₂, the operator f⊗̂g sends completed pure tensors x⊗y to f(x)⊗g(y). Let Φ be the
𝕜-linear map from (E₁→L[𝕜]E₂)⊗(F₁→L[𝕜]F₂) to bounded maps E₁⊗̂F₁→E₂⊗̂F₂, with Φ(f⊗g)=f⊗̂g. For
bounded f:E₁→E₂ and g:F₁→F₂, mapLCompletionLinear(f⊗g)=mapLCompletion f g.
-/
theorem mapLCompletionLinear_tmul (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    mapLCompletionLinear (f ⊗ₜ[𝕜] g) = mapLCompletion f g := rfl

/-- **Algebraic values of the completed finite-operator tensor action.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜 in independent universes, and
write E⊗̂F for the completion of the inner-product tensor norm. For bounded linear f:E₁→E₂ and
g:F₁→F₂, the operator f⊗̂g sends completed pure tensors x⊗y to f(x)⊗g(y). Let Φ be the
𝕜-linear map from (E₁→L[𝕜]E₂)⊗(F₁→L[𝕜]F₂) to bounded maps E₁⊗̂F₁→E₂⊗̂F₂, with Φ(f⊗g)=f⊗̂g. If
z=∑i f_i⊗g_i and u∈E₁⊗F₁, Φ(z)(ι(u)) is the inclusion into E₂⊗̂F₂ of ∑i(f_i⊗g_i)(u), where ι
is the domain completion inclusion and each algebraic factor map sends x⊗y to f_i(x)⊗g_i(y).
-/
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

/-- **Injectivity of the completed finite-operator tensor action.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜 in independent universes, and
write E⊗̂F for the completion of the inner-product tensor norm. For bounded linear f:E₁→E₂ and
g:F₁→F₂, the operator f⊗̂g sends completed pure tensors x⊗y to f(x)⊗g(y). Let Φ be the
𝕜-linear map from (E₁→L[𝕜]E₂)⊗(F₁→L[𝕜]F₂) to bounded maps E₁⊗̂F₁→E₂⊗̂F₂, with Φ(f⊗g)=f⊗̂g. The
map Φ:(E₁→LE₂)⊗(F₁→LF₂)→(E₁⊗̂F₁→LE₂⊗̂F₂) is injective.
-/
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
