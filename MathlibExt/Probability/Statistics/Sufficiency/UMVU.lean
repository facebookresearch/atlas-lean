/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Probability.Moments.Variance
public import MathlibExt.Probability.Statistics.Sufficiency.Complete
public import MathlibExt.Probability.Statistics.Sufficiency.RaoBlackwell
public import MathlibExt.Probability.Statistics.EstimationRisk

/-!
# Lehmann–Scheffé UMVU conclusion

If `S` is sufficient and complete for `P`, every measurable finite-variance unbiased
estimator of `tgt` has a Rao–Blackwell version `φ ∘ S` that is unbiased for `tgt` and has
minimal variance among all measurable finite-variance unbiased estimators of `tgt`.
Without completeness only the weak Rao–Blackwell improvement holds. This is the
minimum-variance conclusion deliberately excluded from `Sufficiency/Complete.lean`;
admissibility is out of scope here.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory ProbabilityTheory Filter Topology MathlibExt.Probability.Statistics.EstimationRisk

open scoped ENNReal

private theorem variance_eq_centered_sq {Ω Θ : Type*} [MeasurableSpace Ω]
    {P : Θ → ProbabilityMeasure Ω} {W : Ω → ℝ} {tgt : Θ → ℝ}
    (hunb : IsUnbiased W P tgt) (hWm : Measurable W) (θ : Θ) :
    ProbabilityTheory.variance W ((P θ) : Measure Ω) =
      ∫ ω, (W ω - tgt θ) ^ 2 ∂((P θ) : Measure Ω) := by
  rw [ProbabilityTheory.variance_eq_integral hWm.aemeasurable, hunb.expect_eq θ]

/-- A Rao–Blackwell version of an unbiased estimator is unbiased. -/
private theorem isUnbiased_raoBlackwell {Ω Θ τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {P : Θ → ProbabilityMeasure Ω} {S : Ω → τ} {W : Ω → ℝ} {tgt : Θ → ℝ}
    (hunb : IsUnbiased W P tgt) {φ : τ → ℝ}
    (hae : ∀ θ, (fun ω => φ (S ω)) =ᵐ[((P θ) : Measure Ω)]
      (((P θ) : Measure Ω)[W | MeasurableSpace.comap S ‹MeasurableSpace τ›]))
    (hmean : ∀ θ, ∫ ω, φ (S ω) ∂((P θ) : Measure Ω) =
      ∫ ω, W ω ∂((P θ) : Measure Ω)) :
    IsUnbiased (fun ω => φ (S ω)) P tgt := by
  intro θ
  refine ⟨?_, ?_⟩
  · exact integrable_condExp.congr (hae θ).symm
  · rw [hmean θ, hunb.expect_eq θ]

-- The `∀`-bound competitor binders under the `∃` are shadowed by tactic intros in every
-- proof, so the statement binders read as unused. Scoped linter exception follows the
-- `FisherInformation.cramerRao` precedent for pinned-but-unused hypotheses.
set_option linter.unusedVariables false in
/-- **Lehmann–Scheffé UMVU conclusion.** If `S` is sufficient and complete for `P`, every
measurable finite-variance unbiased estimator of `tgt` has a Rao–Blackwell version `φ ∘ S`
that is unbiased for `tgt` and has minimal variance among all measurable finite-variance
unbiased estimators of `tgt`. Without completeness only the weak Rao–Blackwell improvement
holds. -/
theorem umvu_of_complete_sufficient
    {Ω Θ τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {P : Θ → ProbabilityMeasure Ω} {S : Ω → τ}
    (hcomplete : IsCompleteStatistic P S)
    (hS : IsSufficient (MeasurableSpace.comap S ‹MeasurableSpace τ›)
      fun θ => ((P θ) : Measure Ω))
    (tgt : Θ → ℝ) {W : Ω → ℝ} (hunb : IsUnbiased W P tgt)
    (hWm : Measurable W) (hW : ∀ θ, MemLp W 2 ((P θ) : Measure Ω)) :
    ∃ φ : τ → ℝ, Measurable φ ∧ IsUnbiased (fun ω => φ (S ω)) P tgt ∧
      (∀ θ, (fun ω => φ (S ω)) =ᵐ[((P θ) : Measure Ω)]
        (((P θ) : Measure Ω)[W | MeasurableSpace.comap S ‹MeasurableSpace τ›])) ∧
      ∀ (W' : Ω → ℝ) (hunb' : IsUnbiased W' P tgt)
        (hWm' : Measurable W') (hW' : ∀ θ, MemLp W' 2 ((P θ) : Measure Ω)) (θ : Θ),
        ProbabilityTheory.variance (fun ω => φ (S ω)) ((P θ) : Measure Ω) ≤
          ProbabilityTheory.variance W' ((P θ) : Measure Ω) := by
  obtain ⟨φ, hφ, hae, hmean, hdecomp⟩ :=
    raoBlackwell_comap hcomplete.1 hS hWm hW tgt
  have hunbφ : IsUnbiased (fun ω => φ (S ω)) P tgt :=
    isUnbiased_raoBlackwell hunb hae hmean
  refine ⟨φ, hφ, hunbφ, hae, fun W' hunb' hWm' hW' θ => ?_⟩
  obtain ⟨ψ, hψ, haeψ, hmeanψ, hdecompψ⟩ :=
    raoBlackwell_comap hcomplete.1 hS hWm' hW' tgt
  have hunbψ : IsUnbiased (fun ω => ψ (S ω)) P tgt :=
    isUnbiased_raoBlackwell hunb' haeψ hmeanψ
  have haeφψ : (fun ω => ψ (S ω)) =ᵐ[((P θ) : Measure Ω)] fun ω => φ (S ω) :=
    hcomplete.ae_eq_of_unbiased tgt hψ hφ hunbψ hunbφ θ
  rw [variance_eq_centered_sq hunbφ (hφ.comp hcomplete.1) θ,
    variance_eq_centered_sq hunb' hWm' θ, hdecompψ θ]
  have hsq : (fun ω => (ψ (S ω) - tgt θ) ^ 2) =ᵐ[((P θ) : Measure Ω)]
      fun ω => (φ (S ω) - tgt θ) ^ 2 := by
    filter_upwards [haeφψ] with ω hω
    rw [hω]
  rw [integral_congr_ae hsq]
  have hnn : 0 ≤ ∫ ω, (W' ω - ψ (S ω)) ^ 2 ∂((P θ) : Measure Ω) := by
    apply integral_nonneg_of_ae
    filter_upwards with ω
    exact sq_nonneg _
  linarith

end MathlibExt.Probability.Statistics.Sufficiency
