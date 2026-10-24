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

open Set

-- Substituting `w = e^z`: `∫_{exp ∘ γ} f(w) dw = ∫_γ f(e^z) e^z dz`.
example {a b : ℂ} (f : ℂ → ℂ) (γ : Path a b)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableWithinAt ℝ γ.extend (Icc 0 1) t) :
    (∫ᶜ w in γ.map' Complex.continuous_exp.continuousOn, f w • ContinuousLinearMap.id ℂ ℂ) =
      ∫ᶜ z in γ, (f (Complex.exp z) * Complex.exp z) • ContinuousLinearMap.id ℂ ℂ := by
  rw [Complex.curveIntegral_map' isOpen_univ Complex.differentiable_exp.differentiableOn γ
    (subset_univ _) hγ]
  simp only [Complex.deriv_exp]

#print axioms Complex.curveIntegral_map'
