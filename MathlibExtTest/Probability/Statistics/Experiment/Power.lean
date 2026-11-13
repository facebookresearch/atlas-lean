/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Power

/-!
# Tests for the law of the known-variance z statistic

Null-case collapse to the standard normal, the variance identity, and the
single-observation shape.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.Experiment

/-- Use: at the null `μ = μ0` the statistic is standard normal. -/
example {n : ℕ} (hn : 0 < n) (μ0 : ℝ) {v : NNReal} (hv : v ≠ 0) :
    HasLaw (zStat n μ0 v) (gaussianReal 0 1)
      (Measure.pi fun _ : Fin n => gaussianReal μ0 v) := by
  have h := hasLaw_zStat hn μ0 μ0 hv
  simpa using h

/-- Use: the variance computation at the heart of the proof. -/
example {n : ℕ} (hn : 0 < n) {v : NNReal} (hv : v ≠ 0) :
    (Real.sqrt (n : ℝ) / Real.sqrt (v : ℝ)) ^ 2 * ((v : ℝ) / (n : ℝ)) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt v.coe_nonneg]
  field_simp

/-- Boundary: at `n = 1` the statistic is the single standardized observation. -/
example (μ0 : ℝ) (v : NNReal) (x : Fin 1 → ℝ) :
    zStat 1 μ0 v x = (x 0 - μ0) / Real.sqrt (v : ℝ) := by
  simp [zStat]

/-- Use: at `δ = 0` the rejection probability is the nominal tail `1 - Φ(c)`. -/
example {n : ℕ} (hn : 0 < n) (μ0 c : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal μ0 v).real (zTestReject n μ0 v c)
      = 1 - cdf (gaussianReal 0 1) c := by
  have h := measureReal_zTestReject hn μ0 0 c hv
  simp only [add_zero, mul_zero, zero_div, sub_zero] at h
  exact h

/-- Boundary: the rejection probability always lies in `[0, 1]`. -/
example {n : ℕ} (_hn : 0 < n) (μ0 δ c : ℝ) {v : NNReal} (_hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real (zTestReject n μ0 v c)
      ∈ Set.Icc 0 1 := by
  rw [Set.mem_Icc]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Control: strict and non-strict cutoffs differ in general (the atom case), so the rejection
set keeps the strict form. -/
example (c : ℝ) : {x : Fin 1 → ℝ | c < x 0} ≠ {x : Fin 1 → ℝ | c ≤ x 0} := by
  intro hcon
  have hmem : (fun _ : Fin 1 => c) ∈ {x : Fin 1 → ℝ | c ≤ x 0} := le_refl c
  rw [← hcon] at hmem
  exact lt_irrefl c hmem

end MathlibExt.Probability.Statistics.Experiment
