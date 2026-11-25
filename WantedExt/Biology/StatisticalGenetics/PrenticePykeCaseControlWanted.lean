/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Logistic incidence models under case-control sampling

Suppose disease incidence follows a logistic model, `P(D = 1 | X = x) = σ(α + β · φ(x))`,
and a case-control study samples cases with probability `π₁` and controls with probability
`π₀`, independently of the covariate `X` given disease status. Then among the sampled
individuals disease still follows a logistic model in `x` with the same coefficients `β`; only
the intercept changes, to `α + log (π₁ / π₀)`. This is the identity behind Prentice and Pyke's
result that prospective logistic regression applied to case-control data estimates the
odds-ratio parameters `β` consistently.

The covariate takes finitely many values here. Prentice and Pyke's further statements, that
the prospective maximum-likelihood estimate of `β` coincides with the semiparametric
retrospective one and has the same asymptotic covariance, are not stated in this module.

Here `σ t = 1 / (1 + exp (-t))` is the logistic function, Mathlib's `Real.sigmoid`.

Sources: R. L. Prentice and R. Pyke, "Logistic disease incidence models and case-control
studies", Biometrika 66 (1979) 403–411.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.PrenticePykeCaseControlWanted

open MeasureTheory

/-- **Case-control sampling shifts only the logistic intercept** (Prentice and Pyke 1979). Let
`μ` be a probability measure on `Ω`, let `X : Ω → 𝒳` be a measurable covariate with values in
a finite type with measurable singletons and features `φ : 𝒳 → ℝ^K`, and let `D` (diseased)
and `S` (sampled) be measurable events. Assume:
* the logistic incidence model: `μ(D ∩ {X = x}) = σ(α + β ⬝ φ(x)) μ({X = x})` for every
  `x`;
* sampling depends on disease status only: `μ(S ∩ D ∩ {X = x}) = π₁ μ(D ∩ {X = x})` and
  `μ(S ∩ Dᶜ ∩ {X = x}) = π₀ μ(Dᶜ ∩ {X = x})` for every `x`, with sampling probabilities
  `0 < π₁ ≤ 1` and `0 < π₀ ≤ 1`.

Then for every covariate value `x` with `μ({X = x}) > 0`, the disease probability among the
sampled, `μ(D ∩ S ∩ {X = x}) / μ(S ∩ {X = x})`, equals `σ(α + log (π₁ / π₀) + β ⬝ φ(x))`.
Here `σ` is the logistic function `Real.sigmoid`.

Source: Prentice and Pyke (1979). -/
public theorem_wanted caseControl_logistic {Ω 𝒳 : Type*} [MeasurableSpace Ω] [Fintype 𝒳]
    [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] {K : ℕ} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → 𝒳) (hX : Measurable X) (φ : 𝒳 → Fin K → ℝ)
    (D S : Set Ω) (hD : MeasurableSet D) (hS : MeasurableSet S) (α : ℝ) (β : Fin K → ℝ)
    (π₀ π₁ : ℝ) (hπ₀ : 0 < π₀) (hπ₀' : π₀ ≤ 1) (hπ₁ : 0 < π₁) (hπ₁' : π₁ ≤ 1)
    (hlogit : ∀ x, μ.real (D ∩ X ⁻¹' {x}) = Real.sigmoid (α + β ⬝ᵥ φ x) * μ.real (X ⁻¹' {x}))
    (hcase : ∀ x, μ.real (S ∩ D ∩ X ⁻¹' {x}) = π₁ * μ.real (D ∩ X ⁻¹' {x}))
    (hcontrol : ∀ x, μ.real (S ∩ Dᶜ ∩ X ⁻¹' {x}) = π₀ * μ.real (Dᶜ ∩ X ⁻¹' {x}))
    (x : 𝒳) (hx : 0 < μ.real (X ⁻¹' {x})) :
    μ.real (D ∩ S ∩ X ⁻¹' {x}) / μ.real (S ∩ X ⁻¹' {x}) =
      Real.sigmoid (α + Real.log (π₁ / π₀) + β ⬝ᵥ φ x)

end WantedExt.Biology.StatisticalGenetics.PrenticePykeCaseControlWanted
