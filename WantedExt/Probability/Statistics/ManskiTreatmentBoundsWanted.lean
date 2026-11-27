/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Manski's no-assumption bounds on the average treatment effect

Let potential outcomes `Y₀, Y₁` take values in `[0, 1]`, and let `T` be the event of treatment.
The data identify `E[Y₁ 1_T]`, `E[Y₀ 1_{Tᶜ}]` and `P(T)`, but not the potential outcomes of the
untreated under treatment or of the treated without it. Since those are between `0` and `1`,
`E[Y₁] ∈ [E[Y₁ 1_T], E[Y₁ 1_T] + P(Tᶜ)]` and `E[Y₀] ∈ [E[Y₀ 1_{Tᶜ}], E[Y₀ 1_{Tᶜ}] + P(T)]`. The
resulting bounds on the average treatment effect `E[Y₁] - E[Y₀]` have width exactly `1` and
always contain `0`, so without further assumptions the data cannot sign the effect. The bounds
are sharp: replacing the unobserved potential outcomes by `0` or `1` keeps the observed data and
attains each end.

Sources: C. F. Manski, "Nonparametric bounds on treatment effects", Am. Econ. Rev. 80(2) (1990)
319–323; C. F. Manski, *Partial Identification of Probability Distributions*, Springer (2003).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.ManskiTreatmentBounds

@[expose] public section

namespace WantedExt.Probability.Statistics.ManskiTreatmentBoundsWanted

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Sharpness of the no-assumption bounds.** Let `μ` be a probability measure on
`Ω`, `T` a measurable event, and `Y₀, Y₁ : Ω → ℝ` measurable with values in `[0, 1]`. Then there
are measurable potential outcomes `Y₀', Y₁'` with values in `[0, 1]` that agree with the observed
ones (`Y₁' = Y₁` on `T` and `Y₀' = Y₀` on `Tᶜ`) and whose average treatment effect equals
`lowerBound μ T Y₀ Y₁`, and likewise a pair whose average treatment effect equals
`upperBound μ T Y₀ Y₁`.

Sources: C. F. Manski, "Nonparametric bounds on treatment effects", Am. Econ. Rev. 80(2) (1990)
319–323. -/
public theorem_wanted bounds_sharp (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Set Ω)
    (hT : MeasurableSet T) (Y₀ Y₁ : Ω → ℝ) (h₀ : Measurable Y₀) (h₁ : Measurable Y₁)
    (h₀01 : ∀ ω, 0 ≤ Y₀ ω ∧ Y₀ ω ≤ 1) (h₁01 : ∀ ω, 0 ≤ Y₁ ω ∧ Y₁ ω ≤ 1) :
    (∃ Y₀' Y₁' : Ω → ℝ, Measurable Y₀' ∧ Measurable Y₁' ∧
        (∀ ω, 0 ≤ Y₀' ω ∧ Y₀' ω ≤ 1) ∧ (∀ ω, 0 ≤ Y₁' ω ∧ Y₁' ω ≤ 1) ∧
        (∀ ω ∈ T, Y₁' ω = Y₁ ω) ∧ (∀ ω ∈ Tᶜ, Y₀' ω = Y₀ ω) ∧
        (∫ ω, Y₁' ω ∂μ) - ∫ ω, Y₀' ω ∂μ = lowerBound μ T Y₀ Y₁) ∧
      ∃ Y₀' Y₁' : Ω → ℝ, Measurable Y₀' ∧ Measurable Y₁' ∧
        (∀ ω, 0 ≤ Y₀' ω ∧ Y₀' ω ≤ 1) ∧ (∀ ω, 0 ≤ Y₁' ω ∧ Y₁' ω ≤ 1) ∧
        (∀ ω ∈ T, Y₁' ω = Y₁ ω) ∧ (∀ ω ∈ Tᶜ, Y₀' ω = Y₀ ω) ∧
        (∫ ω, Y₁' ω ∂μ) - ∫ ω, Y₀' ω ∂μ = upperBound μ T Y₀ Y₁

end WantedExt.Probability.Statistics.ManskiTreatmentBoundsWanted
