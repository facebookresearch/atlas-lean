/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Circle mean for a complex analytic function

If `f : ℂ → ℂ` is analytic on the closed disk of positive radius `r`
centered at `a`, its integral on the circle parameterized by
`a + r exp(iθ)`, for `0 ≤ θ ≤ 2π`, is `2π • f(a)`. The angle integral
uses real Lebesgue measure and the displayed interval orientation.
The radius is strictly positive; the center and function are arbitrary.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Metric

namespace AnalyticL2

/-- For positive radius, the real angle integral from zero to `2π` of the analytic circle values is
`2π` times the center value.

```lean
theorem circle_integral_center (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall a r)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap a r θ)) =
      (2 * Real.pi) • f a
``` -/
theorem circle_integral_center (f : ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOn ℂ f (closedBall a r)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap a r θ)) =
      (2 * Real.pi) • f a := by
  have hDiff : DifferentiableOn ℂ f (closure (ball a |r|)) := by
    simpa only [abs_of_pos hr, closure_ball a hr.ne'] using hf.differentiableOn
  have hMean : Real.circleAverage f a r = f a := hDiff.diffContOnCl.circleAverage
  rw [Real.circleAverage_def] at hMean
  have h := congrArg (fun z : ℂ => (2 * Real.pi) • z) hMean
  simpa only [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    one_smul] using h

end AnalyticL2

end
