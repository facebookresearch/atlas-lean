/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.LaplaceUniqueness

@[expose] public section

noncomputable section

open MeasureTheory

namespace LanglandsTunnell.Converse.MellinUniqueness

-- `exactSource` consumer with the original binders.
example
    (g₁ g₂ : ℝ → ℂ) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (c : ℝ) (Λ : ℂ → ℂ) (hΛ : Differentiable ℂ Λ)
    (hb : Complex.BoundedOnStrips Λ)
    (h₁ : ∀ s : ℂ, c < s.re →
      Integrable (fun t : ℝ => g₁ t * Complex.exp (s * (t : ℂ))) ∧
        ∫ t : ℝ, g₁ t * Complex.exp (s * (t : ℂ)) = Λ s)
    (h₂ : ∀ s : ℂ, s.re < -c →
      Integrable (fun t : ℝ => g₂ t * Complex.exp (s * (t : ℂ))) ∧
        ∫ t : ℝ, g₂ t * Complex.exp (s * (t : ℂ)) = Λ s) :
    g₁ = g₂ :=
  eq_of_laplace_eq_of_boundedOnStrips g₁ g₂ hg₁ hg₂ c Λ hΛ hb h₁ h₂

end LanglandsTunnell.Converse.MellinUniqueness
