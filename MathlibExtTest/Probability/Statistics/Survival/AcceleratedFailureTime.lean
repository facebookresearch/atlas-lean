/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Survival.AcceleratedFailureTime

/-!
# Tests for the accelerated-failure-time model

Probability instance, scaling law, a concrete Weibull survival value under acceleration, the
log-normal parameter map, the hazard transform on an exponential baseline, the quantile transform,
and both sides of the PH-versus-AFT distinction: the Weibull AFT law has a PH reading with an
explicit hazard ratio, the log-normal AFT law has none. Boundary probes: zero baseline survival
cannot discharge the hazard hypothesis, and a negative hazard ratio is no PH reading even where
`S = S₀ ^ c` holds pointwise.
-/

open MeasureTheory ProbabilityTheory Real Set Filter

open scoped NNReal

open MathlibExt.Probability.Statistics.AcceleratedFailureTime

namespace MathlibExtTest.Probability.Statistics.AcceleratedFailureTime

/-- The AFT law of a probability measure is a probability measure. -/
example (η : ℝ) : aftMeasure (logNormalMeasure 0 1) η univ = 1 := measure_univ

/-- Scaling law: two accelerations compose additively in the linear predictor. -/
example (μ₀ : Measure ℝ) : aftMeasure (aftMeasure μ₀ 1) (-1) = μ₀ := by
  rw [aftMeasure_aftMeasure, add_neg_cancel, aftMeasure_zero]

/-- Concrete survival value: Weibull shape `2`, scale `1`, time ratio `2`, at `t = 2`, gives
`exp (-1)`. -/
example : (aftMeasure (weibullMeasure 2 1) (log 2)).real (Ioi 2) = exp (-1) := by
  rw [aftMeasure_weibullMeasure two_pos one_pos, exp_log two_pos, mul_one,
    weibullMeasure_real_Ioi two_pos two_pos two_pos.le, div_self two_ne_zero]
  norm_num

/-- Negative predictor (deceleration toward shorter times): Weibull shape `1`, scale `1`, time
ratio `1 / 2`, at `t = 1`, gives `exp (-2)`. -/
example : (aftMeasure (weibullMeasure 1 1) (-log 2)).real (Ioi 1) = exp (-2) := by
  rw [aftMeasure_real_Ioi, neg_neg, exp_log two_pos, mul_one,
    weibullMeasure_real_Ioi one_pos one_pos two_pos.le, div_one, rpow_one]

/-- Nonpositive time with a negative predictor: the AFT survival function is `1` at `t = -1`. -/
example : (aftMeasure (weibullMeasure 2 1) (-1)).real (Ioi (-1)) = 1 := by
  rw [aftMeasure_weibullMeasure two_pos one_pos]
  have := isProbabilityMeasure_weibullMeasure two_pos (mul_pos (exp_pos (-1)) one_pos)
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, measureReal_def,
    measure_mono_null (Iic_subset_Iic.mpr (by norm_num : (-1 : ℝ) ≤ 0))
      (weibullMeasure_Iic_zero _ _)]
  simp

/-- Log-normal parameter map at concrete values. -/
example : aftMeasure (logNormalMeasure 0 1) 1 = logNormalMeasure 1 1 := by
  rw [aftMeasure_logNormalMeasure, zero_add]

/-- Hazard transform on the unit exponential baseline (Weibull shape `1`, hazard `1`): the AFT law
with predictor `η` has hazard `exp (-η)` at `t = 1`. -/
example (η : ℝ) :
    HasDerivAt (fun s => -log ((aftMeasure (weibullMeasure 1 1) η).real (Ioi s)))
      (exp (-η) * 1) 1 := by
  refine (hasDerivAt_neg_log_aftMeasure_real_Ioi _ η 1 1 ?_ ?_).2
  · rw [weibullMeasure_real_Ioi one_pos one_pos (mul_pos (exp_pos (-η)) one_pos).le]
    exact exp_pos _
  refine (hasDerivAt_id _).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds (mul_pos (exp_pos (-η)) one_pos)] with s hs
  rw [neg_log_weibullMeasure_real_Ioi one_pos one_pos (le_of_lt hs), div_one, rpow_one, id]

/-- Zero survival is rejected: past the end of the support of the Dirac baseline at `0`, the
positivity hypothesis of the hazard and cumulative-hazard transforms cannot be met, so Lean's
`Real.log 0 = 0` is never reported as a hazard. -/
example (η t : ℝ) (ht : 0 < t) : ¬ 0 < (Measure.dirac (0 : ℝ)).real (Ioi (exp (-η) * t)) := by
  have h0 : (0 : ℝ) ∉ Ioi (exp (-η) * t) := fun h =>
    (mul_pos (exp_pos (-η)) ht).not_gt (mem_Ioi.mp h)
  rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Ioi, indicator_of_notMem h0]
  simp

/-- Quantile transform: the baseline distribution function at `q` equals the AFT distribution
function at `exp η * q`. -/
example (η q : ℝ) :
    (aftMeasure (weibullMeasure 2 3) η).real (Iic (exp η * q)) =
      (weibullMeasure 2 3).real (Iic q) :=
  aftMeasure_real_Iic_exp_mul _ η q

/-- Weibull admits the PH reading: shape `2`, time ratio `2` gives hazard ratio `1 / 4`. -/
example : HasProportionalHazards (weibullMeasure 2 1) (aftMeasure (weibullMeasure 2 1) (log 2))
    (1 / 4) := by
  have h := hasProportionalHazards_aftMeasure_weibullMeasure two_pos one_pos (log 2)
  have e : exp (-(2 * log 2)) = 1 / 4 := by
    have : -(2 * log 2) = log (1 / 4) := by
      rw [one_div, log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      push_cast
      ring
    rw [this, exp_log (by norm_num)]
  rwa [e] at h

/-- For the Dirac law at `1`, survival takes only the values `0` and `1` on `[0, ∞)`, so
`S = S ^ (-1)` holds pointwise. -/
example : ∀ t : ℝ, 0 ≤ t →
    (Measure.dirac (1 : ℝ)).real (Ioi t) = (Measure.dirac (1 : ℝ)).real (Ioi t) ^ (-1 : ℝ) := by
  intro t _
  rw [rpow_neg_one, measureReal_def, Measure.dirac_apply' _ measurableSet_Ioi]
  by_cases h : (1 : ℝ) ∈ Ioi t <;> simp [h]

/-- A negative hazard ratio is rejected despite the pointwise identity above. -/
example : ¬ HasProportionalHazards (Measure.dirac (1 : ℝ)) (Measure.dirac 1) (-1) :=
  fun h => absurd h.1 (by norm_num)

/-- Weibull cumulative hazard under acceleration: `H(t | η) = exp (-k η) H₀(t)` at `t = 1`. -/
example (η : ℝ) :
    -log ((aftMeasure (weibullMeasure 3 1) η).real (Ioi 1)) = exp (-(3 * η)) := by
  rw [neg_log_aftMeasure_weibullMeasure_real_Ioi three_pos one_pos zero_le_one,
    neg_log_weibullMeasure_real_Ioi three_pos one_pos zero_le_one, div_one, one_rpow, mul_one]

/-- The log-normal AFT law admits no PH reading for any hazard ratio. -/
example : ¬ ∃ c, HasProportionalHazards (logNormalMeasure 0 1)
    (aftMeasure (logNormalMeasure 0 1) 1) c :=
  fun ⟨c, hc⟩ =>
    not_hasProportionalHazards_aftMeasure_logNormalMeasure 0 one_ne_zero one_ne_zero c hc

/-- The degenerate case is excluded only by hypothesis: with `v = 0` the theorem does not apply,
and the Dirac baseline is handled by `logNormalMeasure_zero_var`. -/
example : aftMeasure (logNormalMeasure 0 0) 1 = Measure.dirac (exp 1) := by
  rw [aftMeasure_logNormalMeasure, zero_add, logNormalMeasure_zero_var]

end MathlibExtTest.Probability.Statistics.AcceleratedFailureTime
