/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Incidence observation intensity

Interval incidence intensity for a nonnegative SIR trajectory:
a reporting fraction of the integrated incidence over an ordered
window plus a background term is a finite nonnegative real, hence
an `NNReal` reporting intensity. Prevalence is not incidence.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Epidemiology.IncidenceObservation.Intensity

set_option linter.unusedVariables false in
/-- **Interval incidence intensity is nonnegative.** For an ordered
window `a ≤ b`, reporting fraction `rho ∈ [0, 1]`, `beta ≥ 0`,
population `N > 0`, nonnegative continuous `S, I` and background
`background ≥ 0`, the real interval intensity
`rho * (∫ t in a..b, beta * S t * I t / N) + background * (b - a)`
is nonnegative, hence packages as an `NNReal` reporting intensity.
Prevalence `I(t)` is not interval incidence. -/
lemma incidence_nonneg {beta rho background N a b : ℝ}
    (hbeta : 0 ≤ beta) (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hN : 0 < N) (hbg : 0 ≤ background) (hab : a ≤ b)
    {S I : ℝ → ℝ} (hS : Continuous S) (hI : Continuous I)
    (hSnn : ∀ t, 0 ≤ S t) (hInn : ∀ t, 0 ≤ I t) :
    0 ≤ rho * (∫ t in a..b, beta * S t * I t / N) + background * (b - a) := by
  have hInt : 0 ≤ ∫ t in a..b, beta * S t * I t / N := by
    apply intervalIntegral.integral_nonneg hab
    intro u _
    exact div_nonneg (mul_nonneg (mul_nonneg hbeta (hSnn u)) (hInn u)) hN.le
  have h1 : 0 ≤ rho * (∫ t in a..b, beta * S t * I t / N) := mul_nonneg hrho0 hInt
  have h2 : 0 ≤ background * (b - a) := mul_nonneg hbg (sub_nonneg.mpr hab)
  exact add_nonneg h1 h2

/-- **Zero-width window.** A zero-width interval has zero incidence
intensity. -/
lemma incidence_zero_width {beta rho background N a : ℝ}
    {S I : ℝ → ℝ} :
    rho * (∫ t in a..a, beta * S t * I t / N) + background * (a - a) = 0 := by
  simp

end MathlibExt.Biology.Epidemiology.IncidenceObservation.Intensity
