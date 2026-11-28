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

import MathlibExt.Analysis.InnerProductSpace.TensorProduct.BilinearMap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Completed tensor actions on sequence-space and zero factors

The finite-support subspace of the complex sequence space ℓ² inherits its
inner-product norm. Its inclusion and a nonreal scalar operator act jointly
on the Hilbert tensor completion.

These examples evaluate pure tensors, retain four independent factor
universes, include a real zero factor, and verify convergence to zero in the
actual operator norm as a complex scalar coefficient tends to zero.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open UniformSpace Filter
open scoped TensorProduct Topology

namespace CompletedTensorBilinearMapSmoke

private abbrev ComplexL2 := lp (fun _ : ℕ => ℂ) 2
private def finiteSupportSubmodule : Submodule ℂ ComplexL2 :=
  Submodule.span ℂ (Set.range fun n : ℕ => lp.single (E := fun _ : ℕ => ℂ) 2 n 1)
private abbrev FiniteSupportL2 := finiteSupportSubmodule
private def embedding : FiniteSupportL2 →L[ℂ] ComplexL2 := finiteSupportSubmodule.subtypeL
private def nonrealScalarMap : ℂ →L[ℂ] ℂ :=
  (1 + Complex.I) • ContinuousLinearMap.id ℂ ℂ

example (x : FiniteSupportL2) (y : ℂ) :
    TensorProduct.mapLCompletionContinuousBilinear embedding nonrealScalarMap
        (x ⊗ₜ[ℂ] y : Completion (FiniteSupportL2 ⊗[ℂ] ℂ)) =
      (x.val ⊗ₜ[ℂ] ((1 + Complex.I) • y) : Completion (ComplexL2 ⊗[ℂ] ℂ)) := by
  rw [TensorProduct.mapLCompletionContinuousBilinear_apply, TensorProduct.mapLCompletion_tmul]
  rfl

universe uE₁ uE₂ uF₁ uF₂

example {E₁ : Type uE₁} {E₂ : Type uE₂} {F₁ : Type uF₁} {F₂ : Type uF₂}
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂]
    (f : E₁ →L[ℂ] E₂) (g : F₁ →L[ℂ] F₂) (x : E₁) (y : F₁) :
    TensorProduct.mapLCompletionContinuousBilinear f ((1 + Complex.I) • g)
        (x ⊗ₜ[ℂ] y : Completion (E₁ ⊗[ℂ] F₁)) =
      (f x ⊗ₜ[ℂ] ((1 + Complex.I) • g y) : Completion (E₂ ⊗[ℂ] F₂)) := by
  rw [TensorProduct.mapLCompletionContinuousBilinear_apply,
    TensorProduct.mapLCompletion_tmul, _root_.smul_apply]

private abbrev ZeroReal := (⊥ : Submodule ℝ ℝ)

example (x : ℝ) (y : ZeroReal) :
    TensorProduct.mapLCompletionContinuousBilinear (ContinuousLinearMap.id ℝ ℝ)
        (0 : ZeroReal →L[ℝ] ℝ) (x ⊗ₜ[ℝ] y : Completion (ℝ ⊗[ℝ] ZeroReal)) =
      (0 : Completion (ℝ ⊗[ℝ] ℝ)) := by
  rw [TensorProduct.mapLCompletionContinuousBilinear_apply, TensorProduct.mapLCompletion_tmul]
  simp only [_root_.zero_apply, TensorProduct.tmul_zero, Completion.coe_zero]

example :
    Tendsto (fun c : ℂ =>
      TensorProduct.mapLCompletionContinuousBilinear (c • embedding) nonrealScalarMap)
      (𝓝 0) (𝓝 (0 : Completion (FiniteSupportL2 ⊗[ℂ] ℂ) →L[ℂ]
        Completion (ComplexL2 ⊗[ℂ] ℂ))) := by
  simp_rw [TensorProduct.mapLCompletionContinuousBilinear_apply,
    TensorProduct.mapLCompletion_smul_left]
  exact (tendsto_id : Tendsto (fun c : ℂ => c) (𝓝 0) (𝓝 0)).zero_smul_const
    (TensorProduct.mapLCompletion embedding nonrealScalarMap)

end CompletedTensorBilinearMapSmoke
