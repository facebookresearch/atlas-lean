/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.LogNormCircleAverage

@[expose] public section

/-- Consumer with the original binders: analyticity on the closed ball and
nonvanishing at the centre give the circle-average inequality. -/
private theorem exactSource {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R :=
  AnalyticOnNhd.log_norm_le_circleAverage_log_norm hF hc

/-- Boundary case `R = 0`: the circle average of `log ‖F‖` over the
degenerate circle is `log ‖F c‖`, so both sides of the inequality agree. -/
example {F : ℂ → ℂ} {c : ℂ} :
    Real.log ‖F c‖ = Real.circleAverage (fun z ↦ Real.log ‖F z‖) c 0 :=
  (Real.circleAverage_zero (f := fun z ↦ Real.log ‖F z‖)).symm

/-- A constant function `fun _ ↦ a` attains equality at every centre and
radius: the circle average of the constant `log ‖a‖` is `log ‖a‖` itself. -/
example (a c : ℂ) (R : ℝ) :
    Real.log ‖a‖ = Real.circleAverage (fun _ : ℂ ↦ Real.log ‖a‖) c R :=
  (Real.circleAverage_const _ c R).symm
