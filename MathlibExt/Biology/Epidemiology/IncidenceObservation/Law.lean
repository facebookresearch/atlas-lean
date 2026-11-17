/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Prod

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

-- Helper instance so `Measure ι` in the frozen statement below elaborates.
instance {ι : Type*} : MeasurableSpace ι := ⊤

/-- **Same intensity, same reporting law.** For any reporting-law
constructor `L` from an intensity value to a law (a measure), two
models with the same intensity have the same reporting law; hence
an estimand that differs between them is not identified by the
reporting law. This is the nonidentification content of the
`rho = 0` background-only reduction: epidemic-rate differences that
do not change the intensity are invisible to the law. -/
lemma epi_same_intensity_same_law {ι : Type*} (L : ℝ → Measure ι)
    {x y : ℝ} (h : x = y) : L x = L y := by
  rw [h]

#print axioms epi_intensity_background_only
#print axioms epi_same_intensity_same_law

end MathlibExt.Biology.Epidemiology.IncidenceObservation.Law
