/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SequentialAnalysis

/-!
# Tests for the objects of sequential analysis

The CUSUM closed form at `n = 1` is Page's first step `max (log L(X₁)) 0`, and the CUSUM
statistic is nonnegative. For the probability laws that the statistics admit, `llr` is the
logarithm of a positive finite likelihood ratio almost surely; an infinite measure such as
`∞ • P₀`, whose likelihood ratio is `∞` almost everywhere, is not admitted. The change-point law
needs both of its laws to be probability measures, and the geometric prior needs `0 < ρ ≤ 1`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.SequentialAnalysis

variable {X : Type*} [MeasurableSpace X] (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
  [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (ω : ℕ → X)

/-- First CUSUM step from the closed form. -/
example : pageCusum P₀ P₁ h₁₀ h₀₁ 1 ω = max (llr P₁ P₀ (ω 0)) 0 := by
  rw [pageCusum_eq_sup]
  simp [Finset.sup'_insert, Finset.range_add_one]
  rw [max_comm]

/-- The CUSUM statistic is nonnegative: the empty final segment contributes `0`. -/
theorem pageCusum_nonneg (n : ℕ) : 0 ≤ pageCusum P₀ P₁ h₁₀ h₀₁ n ω := by
  rw [pageCusum_eq_sup]
  exact Finset.le_sup'_of_le _ (b := n) (by simp) (by simp)

/-- The cumulative log-likelihood ratio is additive in the observations. -/
example (n : ℕ) :
    llrSum P₀ P₁ h₁₀ h₀₁ (n + 1) ω = llrSum P₀ P₁ h₁₀ h₀₁ n ω + llr P₁ P₀ (ω n) := by
  simp [llrSum, Finset.sum_range_succ]

/-- For probability laws with `P₀ ≪ P₁`, the likelihood ratio `dP₁/dP₀` is positive and finite
`P₀`-almost surely, so each term `llr P₁ P₀ x` of `llrSum` is its logarithm. -/
example : ∀ᵐ x ∂P₀, ENNReal.ofReal (Real.exp (llr P₁ P₀ x)) = P₁.rnDeriv P₀ x := by
  filter_upwards [Measure.rnDeriv_pos' h₀₁, Measure.rnDeriv_lt_top P₁ P₀] with x hpos hfin
  rw [llr, Real.exp_log (ENNReal.toReal_pos hpos.ne' hfin.ne), ENNReal.ofReal_toReal hfin.ne]

/-- The point mass and its multiple by `∞` are mutually absolutely continuous, but the likelihood
ratio of the second against the first is `∞`, which `llr` would read as `0`. The second is not a
probability measure, so the log-likelihood ratio sums do not elaborate for this pair. -/
example : ¬ IsProbabilityMeasure ((Measure.dirac ()).withDensity fun _ : Unit ↦ (⊤ : ℝ≥0∞)) := by
  intro h
  have h1 := h.measure_univ
  simp at h1

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure ((Measure.dirac ()).withDensity fun x ↦ ∞)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example
    (h₁₀ : ((Measure.dirac ()).withDensity fun _ : Unit ↦ (⊤ : ℝ≥0∞)) ≪ Measure.dirac ())
    (h₀₁ : Measure.dirac () ≪ (Measure.dirac ()).withDensity fun _ : Unit ↦ (⊤ : ℝ≥0∞)) :
    ℕ → (ℕ → Unit) → ℝ :=
  llrSum (Measure.dirac ()) ((Measure.dirac ()).withDensity fun _ : Unit ↦ (⊤ : ℝ≥0∞)) h₁₀ h₀₁

/-- The change-point law, and the false-alarm and delay criteria built on it, take probability
laws: with zero laws the product law would be the zero measure, so the change-point law does not
elaborate for them. For `ν = 0` every observation has law `P₁`. -/
example : changePointLaw P₀ P₁ 0 = Measure.infinitePi fun _ : ℕ => P₁ := by
  simp [changePointLaw]

/-! Each law needs its own instance: with a zero pre-change law (used here, since the change
point is `2`) or a zero post-change law, the change-point law does not elaborate. -/

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example : Measure (ℕ → Bool) := changePointLaw 0 (Measure.dirac false) 2

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example : Measure (ℕ → Bool) := changePointLaw (Measure.dirac false) 0 1

/-- Under a geometric prior with `0 < ρ ≤ 1`, a procedure that never stops raises no false
alarm. -/
example (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    falseAlarmProb P₀ P₁ ρ hρ₀ hρ₁ (fun _ => ⊤) = 0 := by
  simp [falseAlarmProb]

/-! The geometric prior must be a probability distribution: for `ρ = 0`, under which every
procedure would have false-alarm probability `0`, the proof of `0 < ρ` cannot be given. -/

/--
error: unsolved goals
X : Type u_1
inst✝² : MeasurableSpace X
P₀ P₁ : Measure X
inst✝¹ : IsProbabilityMeasure P₀
inst✝ : IsProbabilityMeasure P₁
h₁₀ : P₁ ≪ P₀
h₀₁ : P₀ ≪ P₁
ω : ℕ → X
⊢ False
-/
#guard_msgs in
noncomputable example : ℝ≥0∞ :=
  falseAlarmProb (Measure.dirac false) (Measure.dirac true) 0 (by norm_num) (by norm_num)
    fun _ => ⊤

end MathlibExtTest.Probability.Statistics.SequentialAnalysis
