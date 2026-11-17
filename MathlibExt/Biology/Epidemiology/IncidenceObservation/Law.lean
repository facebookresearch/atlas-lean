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
public import MathlibExt.Probability.Distributions.PoissonKernel

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
open scoped NNReal

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

/-- The independent Poisson reporting law on a finite interval
index, as a kernel from the intensity vector. -/
noncomputable def reportingLaw {n : ℕ} :
    ProbabilityTheory.Kernel (Fin n → ℝ≥0) (Fin n → ℕ) :=
  ProbabilityTheory.piPoissonKernel (Fin n)

/-- **Law equality from equal intensities.** Two intensity vectors
that agree give the same independent Poisson reporting law. -/
lemma reportingLaw_eq_of_intensity_eq {n : ℕ} {lam lam' : Fin n → ℝ≥0}
    (h : lam = lam') : reportingLaw lam = reportingLaw lam' :=
  congrArg reportingLaw h

/-- **Nonidentification at zero reporting.** With reporting
fraction `rho = 0`, every epidemic rate vector has the same
background-only intensity vector, hence the same Poisson reporting
law; the estimand `tau lam = lam 0` (for `n ≥ 1`) is not identified
by the reporting law: rates `0` and the rate differing only at
coordinate `0` share the law but differ in the estimand. -/
lemma epi_nonidentified_at_zero_reporting {n : ℕ} [NeZero n]
    {background : Fin n → ℝ≥0} :
    ¬ MathlibExt.Probability.Statistics.IsIdentifiedBy
      (fun _lam : Fin n → ℝ≥0 => reportingLaw background)
      (fun lam : Fin n → ℝ≥0 => (lam 0 : ℝ)) := by
  apply MathlibExt.Probability.Statistics.not_isIdentifiedBy_of_eq_of_ne
    (θ := fun _ => (0 : ℝ≥0)) (θ' := fun i => if i = 0 then 1 else 0)
  · rfl
  · simp

end MathlibExt.Biology.Epidemiology.IncidenceObservation.Law
