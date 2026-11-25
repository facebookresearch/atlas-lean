/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.MellinUniqueness

@[expose] public section

noncomputable section

open MeasureTheory

namespace LanglandsTunnell.Converse.MellinUniqueness

-- `exactSource` consumers with the original binders, in `Type`.
example
    (C : Type) [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (f₁ f₂ : C × ℝ → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (c : ℝ)
    (Λ : (C →* ℂˣ) → ℂ → ℂ)
    (hΛ : ∀ χ : C →* ℂˣ, Continuous χ → Differentiable ℂ (Λ χ))
    (hb : ∀ χ : C →* ℂˣ, Continuous χ → Complex.BoundedOnStrips (Λ χ))
    (h₁ : ∀ χ : C →* ℂˣ, Continuous χ → ∀ s : ℂ, c < s.re →
      Integrable
        (fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) *
          Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
        ∫ p : C × ℝ, f₁ p * ((χ p.1 : ℂˣ) : ℂ) *
          Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s)
    (h₂ : ∀ χ : C →* ℂˣ, Continuous χ → ∀ s : ℂ, s.re < -c →
      Integrable
        (fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) *
          Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
        ∫ p : C × ℝ, f₂ p * ((χ p.1 : ℂˣ) : ℂ) *
          Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s) :
    f₁ = f₂ :=
  eq_of_forall_continuous_char_laplace_eq C μ hsep f₁ f₂ hf₁ hf₂ c Λ hΛ hb h₁ h₂

example
    (C : Type) [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (f₁ f₂ : C × ℝ → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (Λ : (C →* ℂˣ) → ℂ → ℂ)
    (hΛ : ∀ χ : C →* ℂˣ, Continuous χ → Differentiable ℂ (Λ χ))
    (hb : ∀ χ : C →* ℂˣ, Continuous χ → Complex.BoundedOnStrips (Λ χ))
    (h : ∀ χ : C →* ℂˣ, Continuous χ → ∃ c : ℝ,
      (∀ s : ℂ, c < s.re →
        Integrable
          (fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) *
            Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
          ∫ p : C × ℝ, f₁ p * ((χ p.1 : ℂˣ) : ℂ) *
            Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s) ∧
      (∀ s : ℂ, s.re < -c →
        Integrable
          (fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) *
            Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
          ∫ p : C × ℝ, f₂ p * ((χ p.1 : ℂˣ) : ℂ) *
            Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s)) :
    f₁ = f₂ :=
  eq_of_forall_continuous_char_exists_laplace_eq C μ hsep f₁ f₂ hf₁ hf₂ Λ hΛ hb h

-- Higher-universe consumer: the same statement over `Type 1`.
example
    (C : Type 1) [Group C] [TopologicalSpace C] [CompactSpace C]
    [MeasurableSpace C] [BorelSpace C] (μ : Measure C) [μ.IsHaarMeasure]
    (hsep : ∀ x : C, x ≠ 1 → ∃ χ : C →* ℂˣ, Continuous χ ∧ χ x ≠ 1)
    (f₁ f₂ : C × ℝ → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (c : ℝ)
    (Λ : (C →* ℂˣ) → ℂ → ℂ)
    (hΛ : ∀ χ : C →* ℂˣ, Continuous χ → Differentiable ℂ (Λ χ))
    (hb : ∀ χ : C →* ℂˣ, Continuous χ → Complex.BoundedOnStrips (Λ χ))
    (h₁ : ∀ χ : C →* ℂˣ, Continuous χ → ∀ s : ℂ, c < s.re →
      Integrable
        (fun p : C × ℝ => f₁ p * ((χ p.1 : ℂˣ) : ℂ) *
          Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
        ∫ p : C × ℝ, f₁ p * ((χ p.1 : ℂˣ) : ℂ) *
          Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s)
    (h₂ : ∀ χ : C →* ℂˣ, Continuous χ → ∀ s : ℂ, s.re < -c →
      Integrable
        (fun p : C × ℝ => f₂ p * ((χ p.1 : ℂˣ) : ℂ) *
          Complex.exp (s * (p.2 : ℂ))) (μ.prod volume) ∧
        ∫ p : C × ℝ, f₂ p * ((χ p.1 : ℂˣ) : ℂ) *
          Complex.exp (s * (p.2 : ℂ)) ∂(μ.prod volume) = Λ χ s) :
    f₁ = f₂ :=
  eq_of_forall_continuous_char_laplace_eq C μ hsep f₁ f₂ hf₁ hf₂ c Λ hΛ hb h₁ h₂

end LanglandsTunnell.Converse.MellinUniqueness
