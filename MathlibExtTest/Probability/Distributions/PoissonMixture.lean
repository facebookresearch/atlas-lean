/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonMixture

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped Nat

namespace MathlibExtTest.Probability.Distributions.PoissonMixture

/-- Non-vacuity: a point mass `δ_m` at `m ≥ 0` satisfies every hypothesis of the mixed Poisson
theorems (probability measure, concentrated on `[0, ∞)`, square-integrable rate). -/
theorem witness_dirac {m : ℝ} (hm : 0 ≤ m) :
    IsProbabilityMeasure (Measure.dirac m) ∧ (∀ᵐ r ∂Measure.dirac m, 0 ≤ r) ∧
      MemLp id 2 (Measure.dirac m) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 hm
  · refine (memLp_const m).ae_eq ?_
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl

/-- With no rate variation (`ν = δ_m`, `m > 0`) the squared coefficient of variation is the
Poisson value `1 / m`. -/
example {m : ℝ} (hm : 0 < m) :
    (∑' k : ℕ, (k : ℝ) ^ 2 * poissonMixtureReal (Measure.dirac m) k -
        (∑' k : ℕ, (k : ℝ) * poissonMixtureReal (Measure.dirac m) k) ^ 2) /
        (∑' k : ℕ, (k : ℝ) * poissonMixtureReal (Measure.dirac m) k) ^ 2 = 1 / m := by
  obtain ⟨_, h0, hmem⟩ := witness_dirac hm.le
  rw [cv_sq_poissonMixture h0 hmem (by simpa using hm)]
  simp

/-- A two-point mixing law `½ δ₀ + ½ δ₂` (a zero-inflated Poisson law) has mean `1` and zero
class `(1 + e^{-2}) / 2 ≥ e^{-1}`. -/
example :
    exp (-1) ≤ poissonMixtureReal ((1 / 2 : ENNReal) • Measure.dirac 0 +
      (1 / 2 : ENNReal) • Measure.dirac 2) 0 := by
  have hprob : IsProbabilityMeasure ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac 2) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.add_halves 1
  have h0 : ∀ᵐ r ∂((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac 2), 0 ≤ r := by
    rw [ae_iff]
    simp
  have hint : Integrable id ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac 2) := by
    refine Integrable.add_measure ?_ ?_ <;>
      exact (integrable_dirac (by simp)).smul_measure (by simp)
  have h := exp_neg_integral_le_poissonMixtureReal_zero h0 hint
  have hmean : ∫ r, r ∂((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac 2) = 1 := by
    rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
      ((integrable_dirac (by simp)).smul_measure (by simp))]
    simp [integral_smul_measure]
  rwa [hmean] at h

/-- Outside the hypotheses the mass function is not a probability mass function: for the zero
measure (not a probability measure) every mass is `0`. -/
example (k : ℕ) : poissonMixtureReal 0 k = 0 := by
  simp [poissonMixtureReal]

end MathlibExtTest.Probability.Distributions.PoissonMixture
