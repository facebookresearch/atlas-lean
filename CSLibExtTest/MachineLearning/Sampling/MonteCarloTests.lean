/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.MonteCarlo

@[expose] public section

/-!
# Tests for Monte Carlo and importance sampling
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Cslib.MachineLearning.Sampling
open scoped Topology ENNReal

namespace CSLibExtTest.MachineLearning.Sampling.MonteCarlo

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Two samples average to their mean. -/
example (f : α → ℝ) (X : ℕ → Ω → α) (ω : Ω) :
    mcEstimate f X 2 ω = (f (X 0 ω) + f (X 1 ω)) / 2 := by
  simp [mcEstimate, Finset.sum_range_succ]
  ring

/-- A constant integrand is estimated exactly from any positive number of samples. -/
example (c : ℝ) (X : ℕ → Ω → α) (ω : Ω) {n : ℕ} (hn : n ≠ 0) :
    mcEstimate (fun _ ↦ c) X n ω = c := by
  simp [mcEstimate]
  field_simp

/-- **Empirical frequencies converge to probabilities**: the Monte Carlo estimate of an indicator
is the fraction of samples landing in `s`, and it converges almost surely to `ν s`. -/
example {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure α} [IsProbabilityMeasure ν]
    {s : Set α} (hs : MeasurableSet s) {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = ν) (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ mcEstimate (s.indicator fun _ ↦ (1 : ℝ)) X n ω) atTop
      (𝓝 (ν.real s)) := by
  have h := tendsto_mcEstimate (measurable_const.indicator hs)
    ((integrable_const (1 : ℝ)).indicator hs) hX hlaw hindep
  simpa [integral_indicator hs] using h

/-- Importance weights reweight the proposal into the target: with weight `2` on a probability
measure `ρ`, the target `2 ρ` integrates `f` to twice its `ρ`-integral. -/
example {ρ : Measure α} [IsProbabilityMeasure ρ] (f : α → ℝ) :
    ∫ x, (2 : ℝ≥0∞).toReal * f x ∂ρ = ∫ x, f x ∂(ρ.withDensity fun _ ↦ 2) :=
  integral_weight_mul measurable_const (ae_of_all _ fun _ ↦ ENNReal.ofNat_lt_top) f

/-! ### Importance sampling for an integrand that is only integrable -/

section IntegrableImportanceSampling

variable {μ : Measure Ω}

/-- With weight `1`, unbiasedness is plain Monte Carlo for an integrable-only integrand. -/
example {ρ : Measure α} {f : α → ℝ} (hfi : Integrable f ρ) {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ρ) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, mcEstimate f X n ω ∂μ = ∫ x, f x ∂ρ := by
  have h := integral_isEstimate_of_integrable (μ := μ) (w := 1) measurable_const
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.one_lt_top) (by rwa [withDensity_one]) hX hlaw hn
  simpa only [isEstimate_one, withDensity_one] using h

/-- The measurable-integrand theorem is the special case of the integrable one. -/
example {ρ : Measure α} {w : α → ℝ≥0∞} (hw : Measurable w) (hwt : ∀ᵐ x ∂ρ, w x < ∞) {f : α → ℝ}
    (hf : Measurable f) (hfi : Integrable f (ρ.withDensity w)) {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ρ) {n : ℕ} (hn : n ≠ 0) :
    integral_isEstimate_of_integrable (μ := μ) hw hwt hfi hX hlaw hn =
      integral_isEstimate hw hwt hf hfi hX hlaw hn := rfl

/-- At `n = 0` the estimate is `0`, so `n ≠ 0` cannot be dropped. -/
example (X : ℕ → Ω → α) (w : α → ℝ≥0∞) (f : α → ℝ) (ω : Ω) : isEstimate w f X 0 ω = 0 := by
  simp [isEstimate, mcEstimate]

/-- Radon–Nikodym form: a target `ν ≪ ρ` sampled through `ν.rnDeriv ρ`. -/
example {ν ρ : Measure α} [SigmaFinite ν] [SigmaFinite ρ] (hνρ : ν ≪ ρ) {f : α → ℝ}
    (hfi : Integrable f ν) {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = ρ) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, isEstimate (ν.rnDeriv ρ) f X n ω ∂μ = ∫ x, f x ∂ν :=
  integral_isEstimate_rnDeriv (μ := μ) hνρ hfi hX hlaw hn

#print axioms integral_isEstimate_of_integrable
#print axioms tendsto_isEstimate_of_integrable
#print axioms integral_isEstimate_rnDeriv
#print axioms tendsto_isEstimate_rnDeriv
#print axioms isEstimate_one

end IntegrableImportanceSampling
/-- The integrable-integrand variants need no `Measurable f` hypothesis. -/
example {μ : Measure Ω} {ν : Measure α} {f : α → ℝ} (hfi : Integrable f ν) {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ν)
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) {n : ℕ} (hn : n ≠ 0) :
    (∫ ω, mcEstimate f X n ω ∂μ = ∫ x, f x ∂ν) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k ↦ mcEstimate f X k ω) atTop (𝓝 (∫ x, f x ∂ν)) :=
  ⟨integral_mcEstimate_of_integrable hfi hX hlaw hn,
    tendsto_mcEstimate_of_integrable hfi hX hlaw hindep⟩

example {μ : Measure Ω} {ν : Measure α} {f g : α → ℝ} (hfg : f =ᵐ[ν] g) {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ν) :
    ∀ᵐ ω ∂μ, ∀ n, mcEstimate f X n ω = mcEstimate g X n ω :=
  mcEstimate_ae_eq hfg hX hlaw

#print axioms integral_mcEstimate_of_integrable
#print axioms tendsto_mcEstimate_of_integrable
#print axioms mcEstimate_ae_eq

end CSLibExtTest.MachineLearning.Sampling.MonteCarlo
