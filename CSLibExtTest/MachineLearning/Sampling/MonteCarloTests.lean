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

end CSLibExtTest.MachineLearning.Sampling.MonteCarlo
