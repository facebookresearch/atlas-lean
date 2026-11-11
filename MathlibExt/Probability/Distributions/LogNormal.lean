/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The log-normal law

`logNormalMeasure μ v` is the law of `exp Y` for `Y ~ N(μ, v)`, defined as the pushforward of
`gaussianReal μ v` along `Real.exp`. The parameters are those of the underlying Gaussian: `μ` is
the mean and `v` the variance of `log X`, not of `X`. No density is constructed.

## Main results

* `ProbabilityTheory.isProbabilityMeasure_logNormalMeasure`.
* `ProbabilityTheory.logNormalMeasure_Iic_zero`: no mass on `(-∞, 0]`.
* `ProbabilityTheory.logNormalMeasure_real_Iic`: `P(X ≤ t) = P(Y ≤ log t)` for `t > 0`.
* `ProbabilityTheory.integral_id_logNormalMeasure`: the mean is `exp(μ + v / 2)`, from the
  Gaussian moment generating function at `1`.
-/

open MeasureTheory Set Real

open scoped NNReal

namespace ProbabilityTheory

@[expose] public section

noncomputable section

/-- **The log-normal law** with log-mean `μ` and log-variance `v`: the pushforward of the
Gaussian `gaussianReal μ v` along `Real.exp`. -/
def logNormalMeasure (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  (gaussianReal μ v).map exp

instance isProbabilityMeasure_logNormalMeasure (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (logNormalMeasure μ v) :=
  inferInstanceAs (IsProbabilityMeasure ((gaussianReal μ v).map exp))

/-- The log-normal law puts no mass on `(-∞, 0]`. -/
theorem logNormalMeasure_Iic_zero (μ : ℝ) (v : ℝ≥0) : logNormalMeasure μ v (Iic 0) = 0 := by
  rw [logNormalMeasure, Measure.map_apply measurable_exp measurableSet_Iic]
  have : exp ⁻¹' Iic 0 = ∅ := eq_empty_of_forall_notMem fun y hy => (exp_pos y).not_ge hy
  simp [this]

/-- **Log-normal CDF**: for `t > 0`, `P(X ≤ t) = P(Y ≤ log t)` with `Y ~ N(μ, v)`. -/
theorem logNormalMeasure_real_Iic (μ : ℝ) (v : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    (logNormalMeasure μ v).real (Iic t) = (gaussianReal μ v).real (Iic (log t)) := by
  rw [logNormalMeasure, map_measureReal_apply measurable_exp measurableSet_Iic]
  congr 1
  ext y
  exact (le_log_iff_exp_le ht).symm

/-- **Log-normal mean**: `E[X] = exp(μ + v / 2)`, the Gaussian moment generating function
`mgf_id_gaussianReal` at `1`. -/
theorem integral_id_logNormalMeasure (μ : ℝ) (v : ℝ≥0) :
    ∫ x, x ∂(logNormalMeasure μ v) = exp (μ + v / 2) := by
  rw [logNormalMeasure, integral_map (f := fun x : ℝ => x) measurable_exp.aemeasurable
    aestronglyMeasurable_id]
  have h := congrFun (mgf_id_gaussianReal (μ := μ) (v := v)) 1
  simp only [mgf, id, one_mul, mul_one, one_pow] at h
  exact h

end

end

end ProbabilityTheory
