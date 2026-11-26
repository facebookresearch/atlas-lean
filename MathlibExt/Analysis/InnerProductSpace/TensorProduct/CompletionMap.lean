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

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Bounded maps on Hilbert tensor completions

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). The operator norm satisfies ‖f⊗̂g‖≤‖f‖‖g‖. This operation is bilinear in f,g,
preserves identities and zero factors, and respects factorwise composition. Completeness is
supplied by the tensor completions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open UniformSpace
open scoped TensorProduct

namespace TensorProduct

universe u𝕜 uE₁ uE₂ uE₃ uF₁ uF₂ uF₃

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
variable {F₂ : Type uF₂} [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- **Completed tensor map of two bounded operators.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). The bounded linear map mapLCompletion f g:E₁⊗̂F₁→E₂⊗̂F₂ is f⊗̂g.
-/
def mapLCompletion (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) :=
  (mapL f g).completion

/-- **Completed tensor map on an algebraic tensor.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). For z∈E₁⊗F₁ and the canonical tensor inclusions ι₁,ι₂, mapLCompletion f g
(ι₁(z))=ι₂((f⊗g)(z)).
-/
@[simp]
theorem mapLCompletion_coe (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂)
    (u : E₁ ⊗[𝕜] F₁) :
    mapLCompletion f g (u : Completion (E₁ ⊗[𝕜] F₁)) =
      (mapL f g u : Completion (E₂ ⊗[𝕜] F₂)) :=
  ContinuousLinearMap.completion_apply_coe (mapL f g) u

/-- **Pure tensor formula for a completed operator tensor.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). For x∈E₁ and y∈F₁, mapLCompletion f g (x⊗y)=f(x)⊗g(y), with both pure tensors
viewed in their completions.
-/
theorem mapLCompletion_tmul (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂)
    (x : E₁) (y : F₁) :
    mapLCompletion f g (x ⊗ₜ[𝕜] y : Completion (E₁ ⊗[𝕜] F₁)) =
      (f x ⊗ₜ[𝕜] g y : Completion (E₂ ⊗[𝕜] F₂)) := by
  rw [mapLCompletion_coe, mapL_tmul]

/-- **Product upper bound for the completed tensor operator norm.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). The norm estimate is ‖mapLCompletion f g‖≤‖f‖‖g‖.
-/
theorem norm_mapLCompletion_le (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    ‖mapLCompletion f g‖ ≤ ‖f‖ * ‖g‖ := by
  refine (mapLCompletion f g).opNorm_le_bound
    (mul_nonneg (norm_nonneg f) (norm_nonneg g)) ?_
  intro z
  refine Completion.induction_on z (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro u
  simpa only [mapLCompletion_coe, Completion.norm_coe] using
    (mapL f g).le_of_opNorm_le (norm_mapL_le f g) u

variable (𝕜 E₁ F₁) in
/-- **Identity maps on the tensor completion.**

Let E,F be inner product spaces over an RCLike field 𝕜, and let E⊗̂F be their Hilbert tensor
completion. Then mapLCompletion id_E id_F=id_(E⊗̂F).
-/
@[simp]
theorem mapLCompletion_id_id :
    mapLCompletion (ContinuousLinearMap.id 𝕜 E₁) (ContinuousLinearMap.id 𝕜 F₁) =
      ContinuousLinearMap.id 𝕜 (Completion (E₁ ⊗[𝕜] F₁)) := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_id_id, ContinuousLinearMap.id_apply]

/-- **Zero in the first completed operator tensor factor.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). For g:F₁→F₂, mapLCompletion (0:E₁→E₂) g=0.
-/
@[simp]
theorem mapLCompletion_zero_left (g : F₁ →L[𝕜] F₂) :
    mapLCompletion (0 : E₁ →L[𝕜] E₂) g = 0 := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_zero_left, zero_apply,
    Completion.coe_zero]

/-- **Zero in the second completed operator tensor factor.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). For f:E₁→E₂, mapLCompletion f (0:F₁→F₂)=0.
-/
@[simp]
theorem mapLCompletion_zero_right (f : E₁ →L[𝕜] E₂) :
    mapLCompletion f (0 : F₁ →L[𝕜] F₂) = 0 := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_zero_right, zero_apply,
    Completion.coe_zero]

/-- **Additivity in the first completed operator tensor factor.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). For bounded f₁,f₂:E₁→E₂, (f₁+f₂)⊗̂g=f₁⊗̂g+f₂⊗̂g.
-/
theorem mapLCompletion_add_left (f₁ f₂ : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    mapLCompletion (f₁ + f₂) g = mapLCompletion f₁ g + mapLCompletion f₂ g := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_add_left, add_apply,
    Completion.coe_add]

/-- **Additivity in the second completed operator tensor factor.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). For bounded g₁,g₂:F₁→F₂, f⊗̂(g₁+g₂)=f⊗̂g₁+f⊗̂g₂.
-/
theorem mapLCompletion_add_right (f : E₁ →L[𝕜] E₂) (g₁ g₂ : F₁ →L[𝕜] F₂) :
    mapLCompletion f (g₁ + g₂) = mapLCompletion f g₁ + mapLCompletion f g₂ := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_add_right, add_apply,
    Completion.coe_add]

/-- **Scalar linearity in the first completed operator tensor factor.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). For c∈𝕜, (c•f)⊗̂g=c•(f⊗̂g).
-/
theorem mapLCompletion_smul_left (c : 𝕜) (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    mapLCompletion (c • f) g = c • mapLCompletion f g := by
  change (mapL (c • f) g).completion = c • (mapL f g).completion
  rw [mapL_smul_left]
  apply ContinuousLinearMap.coeFn_injective
  funext z
  change Completion.map (fun u : E₁ ⊗[𝕜] F₁ => c • mapL f g u) z =
    c • Completion.map (mapL f g) z
  rw [Completion.smul_def]
  exact (congr_fun (Completion.map_comp
    (uniformContinuous_const_smul c) (mapL f g).uniformContinuous) z).symm

/-- **Scalar linearity in the second completed operator tensor factor.**

Let E₁,E₂,F₁,F₂ be inner product spaces over an RCLike field 𝕜, with independent universes.
Write E⊗̂F for the completion of their algebraic tensor with the inner-product tensor norm.
For bounded 𝕜-linear f:E₁→E₂ and g:F₁→F₂, write f⊗̂g for the completed tensor map sending x⊗y
to f(x)⊗g(y). For c∈𝕜, f⊗̂(c•g)=c•(f⊗̂g).
-/
theorem mapLCompletion_smul_right (c : 𝕜) (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    mapLCompletion f (c • g) = c • mapLCompletion f g := by
  change (mapL f (c • g)).completion = c • (mapL f g).completion
  rw [mapL_smul_right]
  apply ContinuousLinearMap.coeFn_injective
  funext z
  change Completion.map (fun u : E₁ ⊗[𝕜] F₁ => c • mapL f g u) z =
    c • Completion.map (mapL f g) z
  rw [Completion.smul_def]
  exact (congr_fun (Completion.map_comp
    (uniformContinuous_const_smul c) (mapL f g).uniformContinuous) z).symm

section Composition

variable {E₃ : Type uE₃} [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
variable {F₃ : Type uF₃} [NormedAddCommGroup F₃] [InnerProductSpace 𝕜 F₃]

/-- **Factorwise composition of completed tensor operators.**

Let E₁,E₂,E₃,F₁,F₂,F₃ be inner product spaces over an RCLike field 𝕜 in independent universes.
For bounded linear maps f₁:E₁→E₂, f₂:E₂→E₃, g₁:F₁→F₂ and g₂:F₂→F₃,
(f₂∘f₁)⊗̂(g₂∘g₁)=(f₂⊗̂g₂)∘(f₁⊗̂g₁) on the Hilbert tensor completions.
-/
theorem mapLCompletion_comp (f₂ : E₂ →L[𝕜] E₃) (f₁ : E₁ →L[𝕜] E₂)
    (g₂ : F₂ →L[𝕜] F₃) (g₁ : F₁ →L[𝕜] F₂) :
    mapLCompletion (f₂.comp f₁) (g₂.comp g₁) =
      (mapLCompletion f₂ g₂).comp (mapLCompletion f₁ g₁) := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_comp, ContinuousLinearMap.comp_apply]

end Composition

/-- **Multiplication of completed tensor endomorphisms.**

Let E,F be inner product spaces over an RCLike field 𝕜. For bounded endomorphisms f₁,f₂ of E
and g₁,g₂ of F, mapLCompletion(f₁*f₂)(g₁*g₂)=mapLCompletion f₁ g₁*mapLCompletion f₂ g₂, where
* is operator composition.
-/
theorem mapLCompletion_mul (f₁ f₂ : E₁ →L[𝕜] E₁) (g₁ g₂ : F₁ →L[𝕜] F₁) :
    mapLCompletion (f₁ * f₂) (g₁ * g₂) =
      mapLCompletion f₁ g₁ * mapLCompletion f₂ g₂ :=
  mapLCompletion_comp f₁ f₂ g₁ g₂

end TensorProduct
