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
theorem exactSource {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |R|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c R :=
  AnalyticOnNhd.log_norm_le_circleAverage_log_norm hF hc

/-- Boundary case `R = 0`: both sides reduce to `log ‖F c‖`. -/
example {F : ℂ → ℂ} {c : ℂ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall c |(0 : ℝ)|)) (hc : F c ≠ 0) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z ↦ Real.log ‖F z‖) c 0 :=
  exactSource hF hc

/-- A nonzero constant function attains equality: the average of the
constant `log ‖F‖` is `log ‖F c‖` itself. -/
example :
    Real.log ‖(1 : ℂ)‖ ≤
      Real.circleAverage (fun _ : ℂ ↦ Real.log ‖(1 : ℂ)‖) 0 1 := by
  apply exactSource (F := fun _ ↦ 1) (c := 0) (R := 1)
  · exact analyticOnNhd_const
  · simp
