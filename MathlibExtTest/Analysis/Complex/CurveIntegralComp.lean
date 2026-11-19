/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MathlibExt.Analysis.Complex.CurveIntegralComp

set_option autoImplicit false

open Set MeasureTheory
open scoped unitInterval

-- Substituting `w = e^z`: `∫_{exp ∘ γ} f(w) dw = ∫_γ f(e^z) e^z dz`, for a path that is
-- differentiable at almost every time.
example {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b)
    (hγ : ∀ᵐ t, t ∈ I → DifferentiableAt ℝ γ.extend t) :
    (∫ᶜ w in γ.map' Complex.continuous_exp.continuousOn, f w • ContinuousLinearMap.id ℂ ℂ) =
      ∫ᶜ z in γ, (f (Complex.exp z) * Complex.exp z) • ContinuousLinearMap.id ℂ ℂ := by
  rw [Complex.curveIntegral_map'_eq_comp_mul_deriv f γ isOpen_univ
    Complex.differentiable_exp.differentiableOn (subset_univ _) hγ]
  simp only [Complex.deriv_exp]

#print axioms Complex.curveIntegral_map'_eq_comp_mul_deriv
