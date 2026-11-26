/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic.NormNum

/-! # Binary populations with identical margins and opposite covariances -/

open MeasureTheory ProbabilityTheory unitInterval

namespace MetaMathlibExt

/-- **Group margins do not determine individual associations.** The equally weighted
populations `[(1, 1), (0, 0)]` and `[(1, 0), (0, 1)]` each give both coordinates the fair
binary law on `0` and `1`. Their covariances are `1/4` and `-1/4`, respectively, so the
joint laws are distinct. This example illustrates the distinction between aggregate
and individual associations discussed in D. A. Freedman, *The Ecological Fallacy*. -/
public theorem group_margins_do_not_determine_individual_associations :
    let half : I := ⟨1 / 2, by constructor <;> norm_num⟩
    let aligned : Measure (ℝ × ℝ) := bernoulliMeasure (1, 1) (0, 0) half
    let crossed : Measure (ℝ × ℝ) := bernoulliMeasure (1, 0) (0, 1) half
    let marginal : Measure ℝ := bernoulliMeasure 1 0 half
    aligned.map Prod.fst = marginal ∧ aligned.map Prod.snd = marginal ∧
      crossed.map Prod.fst = marginal ∧ crossed.map Prod.snd = marginal ∧
      covariance Prod.fst Prod.snd aligned = 1 / 4 ∧
      covariance Prod.fst Prod.snd crossed = -(1 / 4) ∧ aligned ≠ crossed := by
  intro half aligned crossed marginal
  have hhalf : unitInterval.symm half = half := by
    apply Subtype.ext
    norm_num [half, unitInterval.symm]
  have hswap : bernoulliMeasure (0 : ℝ) 1 half = marginal := by
    rw [show marginal = bernoulliMeasure 1 0 half from rfl]
    simp only [bernoulliMeasure_def, hhalf, add_comm]
  have ha : covariance Prod.fst Prod.snd aligned = 1 / 4 := by
    norm_num [aligned, half, covariance, integral_bernoulliMeasure, smul_eq_mul]
  have hc : covariance Prod.fst Prod.snd crossed = -(1 / 4) := by
    norm_num [crossed, half, covariance, integral_bernoulliMeasure, smul_eq_mul]
  refine ⟨by simp [aligned, marginal], by simp [aligned, marginal],
    by simp [crossed, marginal], ?_, ha, hc, ?_⟩
  · simpa only [crossed, map_bernoulliMeasure] using hswap
  · intro h
    rw [h, hc] at ha
    norm_num at ha

end MetaMathlibExt
