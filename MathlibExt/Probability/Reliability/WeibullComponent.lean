/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Distributions.Weibull

/-!
# Weibull component survival

Component-level readings of the Weibull lifetime law: for positive
shape `k` and scale `l`, the survival probability at time `t ≥ 0`
is `exp (-(t / l) ^ k)` (strictly positive, at most one); shape
one gives the exponential survival `exp (-t / l)`; nonpositive
shape or scale gives the zero measure, so invalid parameters are
rejected rather than reinterpreted.

## Main results

- `Reliability.weibull_component_survival`: the survival formula
  with positivity and the unit bound.
- `Reliability.weibull_component_exponential`: the shape-one
  exponential case.
- `Reliability.weibull_invalid_parameters`: invalid parameters
  give the zero measure.
-/

@[expose] public section

namespace Reliability

open ProbabilityTheory Set MeasureTheory

/-- Component survival under a Weibull lifetime law: for positive
shape `k` and scale `l`, the survival probability at time `t ≥ 0`
is `exp (-(t / l) ^ k)`, it is strictly positive, and it is at most
one. This is the component-level reading of the Weibull survival
tail: the lifetime event `{X > t}` uses the same parameters. -/
theorem weibull_component_survival {k l t : ℝ} (hk : 0 < k)
    (hl : 0 < l) (ht : 0 ≤ t) :
    (weibullMeasure k l).real (Ioi t) = Real.exp (-(t / l) ^ k)
      ∧ 0 < (weibullMeasure k l).real (Ioi t)
      ∧ (weibullMeasure k l).real (Ioi t) ≤ 1 := by
  have h_eq := weibullMeasure_real_Ioi hk hl ht
  have := isProbabilityMeasure_weibullMeasure hk hl
  refine ⟨h_eq, ?_, ?_⟩
  · rw [h_eq]
    exact Real.exp_pos _
  · exact measureReal_le_one

/-- Exponential special case: shape `k = 1` gives survival
`exp (-t / l)`. -/
theorem weibull_component_exponential {l t : ℝ} (hl : 0 < l)
    (ht : 0 ≤ t) :
    (weibullMeasure 1 l).real (Ioi t) = Real.exp (-t / l) := by
  have h := weibullMeasure_real_Ioi one_pos hl ht
  rw [h, Real.rpow_one, neg_div']

/-- Invalid parameters give the zero measure: a nonpositive shape
or scale is rejected rather than silently reinterpreted. -/
theorem weibull_invalid_parameters {k l : ℝ}
    (h : ¬ (0 < k ∧ 0 < l)) : weibullMeasure k l = 0 := by
  unfold weibullMeasure
  exact ite_eq_right h

end Reliability
