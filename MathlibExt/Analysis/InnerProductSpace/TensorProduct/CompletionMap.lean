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
# Bounded maps on completed Hilbert tensors

The carrier is the stock uniform completion of the algebraic tensor equipped
with its stock inner-product norm. Bounded maps on the factors act on this
completion through `ContinuousLinearMap.completion`.
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

/-- The bounded tensor map between the literal stock Hilbert completions. -/
def mapLCompletion (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂) :=
  (mapL f g).completion

/-- The completed map extends the original bounded algebraic tensor map. -/
@[simp]
theorem mapLCompletion_coe (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂)
    (u : E₁ ⊗[𝕜] F₁) :
    mapLCompletion f g (u : Completion (E₁ ⊗[𝕜] F₁)) =
      (mapL f g u : Completion (E₂ ⊗[𝕜] F₂)) :=
  ContinuousLinearMap.completion_apply_coe (mapL f g) u

/-- On a pure tensor, the completed map applies the two factor maps. -/
theorem mapLCompletion_tmul (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂)
    (x : E₁) (y : F₁) :
    mapLCompletion f g (x ⊗ₜ[𝕜] y : Completion (E₁ ⊗[𝕜] F₁)) =
      (f x ⊗ₜ[𝕜] g y : Completion (E₂ ⊗[𝕜] F₂)) := by
  rw [mapLCompletion_coe, mapL_tmul]

/-- Completion retains the product upper bound for the operator norm. -/
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
/-- Identity factor maps induce the identity on the completed tensor. -/
@[simp]
theorem mapLCompletion_id_id :
    mapLCompletion (ContinuousLinearMap.id 𝕜 E₁) (ContinuousLinearMap.id 𝕜 F₁) =
      ContinuousLinearMap.id 𝕜 (Completion (E₁ ⊗[𝕜] F₁)) := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_id_id, ContinuousLinearMap.id_apply]

/-- A zero first factor induces the zero completed tensor map. -/
@[simp]
theorem mapLCompletion_zero_left (g : F₁ →L[𝕜] F₂) :
    mapLCompletion (0 : E₁ →L[𝕜] E₂) g = 0 := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_zero_left, zero_apply,
    Completion.coe_zero]

/-- A zero second factor induces the zero completed tensor map. -/
@[simp]
theorem mapLCompletion_zero_right (f : E₁ →L[𝕜] E₂) :
    mapLCompletion f (0 : F₁ →L[𝕜] F₂) = 0 := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_zero_right, zero_apply,
    Completion.coe_zero]

/-- The completed tensor map is additive in its first operator. -/
theorem mapLCompletion_add_left (f₁ f₂ : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    mapLCompletion (f₁ + f₂) g = mapLCompletion f₁ g + mapLCompletion f₂ g := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_add_left, add_apply,
    Completion.coe_add]

/-- The completed tensor map is additive in its second operator. -/
theorem mapLCompletion_add_right (f : E₁ →L[𝕜] E₂) (g₁ g₂ : F₁ →L[𝕜] F₂) :
    mapLCompletion f (g₁ + g₂) = mapLCompletion f g₁ + mapLCompletion f g₂ := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_add_right, add_apply,
    Completion.coe_add]

/-- The completed tensor map is scalar linear in its first operator. -/
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

/-- The completed tensor map is scalar linear in its second operator. -/
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

/-- Composition is performed separately in the two factors. -/
theorem mapLCompletion_comp (f₂ : E₂ →L[𝕜] E₃) (f₁ : E₁ →L[𝕜] E₂)
    (g₂ : F₂ →L[𝕜] F₃) (g₁ : F₁ →L[𝕜] F₂) :
    mapLCompletion (f₂.comp f₁) (g₂.comp g₁) =
      (mapLCompletion f₂ g₂).comp (mapLCompletion f₁ g₁) := by
  ext z
  refine Completion.induction_on z (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u
  simp only [mapLCompletion_coe, mapL_comp, ContinuousLinearMap.comp_apply]

end Composition

/-- Multiplication of factor endomorphisms becomes composition of completed maps. -/
theorem mapLCompletion_mul (f₁ f₂ : E₁ →L[𝕜] E₁) (g₁ g₂ : F₁ →L[𝕜] F₁) :
    mapLCompletion (f₁ * f₂) (g₁ * g₂) =
      mapLCompletion f₁ g₁ * mapLCompletion f₂ g₂ :=
  mapLCompletion_comp f₁ f₂ g₁ g₂

end TensorProduct
