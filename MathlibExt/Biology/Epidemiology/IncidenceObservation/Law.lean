/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import MathlibExt.Probability.Statistics.Identifiability

/-!
# Epidemic reporting law

The independent Poisson reporting law over intervals is determined
by the interval intensities. At reporting fraction rho = 0 the
intensity is background-only: it depends on the fixed background
and interval widths, not on the epidemic rates. Two models with
the same intensity have the same reporting law, so an estimand
varying between them is not identified. Reporting independence
and Poisson dispersion are modeling assumptions, not consequences
of the SIR ODE.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Epidemiology.IncidenceObservation.Law

/-- **Background-only reporting intensity at `rho = 0`.** When the
reporting fraction is zero, the interval intensity
`rho * (∫ t in a..b, beta * S t * I t / N) + background * (b - a)`
reduces to the background term alone: at `rho = 0` the reporting
intensity depends only on the fixed background and the interval
width, not on the epidemic rates (`beta`, the trajectory, or `N`). -/
lemma epi_intensity_background_only {beta background N a b : ℝ}
    {S I : ℝ → ℝ} :
    (0 : ℝ) * (∫ t in a..b, beta * S t * I t / N) + background * (b - a) =
      background * (b - a) := by
  rw [zero_mul, zero_add]

/-- **Nonidentification at zero reporting.** Let the model be a
rate `beta` with a fixed background/window intensity map, the
reporting law `fun beta => L (background * (b - a))` (the `rho = 0`
law, independent of `beta`), and the estimand `tau beta = beta`.
Then the estimand is not identified by the reporting law: the two
distinct rates `0` and `1` have the same law but different
estimands. -/
lemma epi_nonidentified_at_zero_reporting {ι : Type*} [MeasurableSpace ι] (L : ℝ → Measure ι) {background a b : ℝ} :
    ¬ MathlibExt.Probability.Statistics.IsIdentifiedBy
      (fun beta : ℝ => L ((0 : ℝ) * beta + background * (b - a)))
      (fun beta : ℝ => beta) := by
  apply MathlibExt.Probability.Statistics.not_isIdentifiedBy_of_eq_of_ne
    (θ := (0 : ℝ)) (θ' := (1 : ℝ))
  · simp
  · norm_num

end MathlibExt.Biology.Epidemiology.IncidenceObservation.Law
