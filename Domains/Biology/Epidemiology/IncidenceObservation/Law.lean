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

/-- The interval-intensity vector at reporting fraction `rho`,
with `rho ≤ 1`: background plus `rho` times the integrated epidemic
incidence per interval. -/
noncomputable def intensityAt {n : ℕ} (rho : ℝ≥0) (hrho : rho ≤ 1)
    (background : Fin n → ℝ≥0) (incidence : Fin n → ℝ≥0) :
    Fin n → ℝ≥0 :=
  fun j => background j + rho * incidence j

/-- At zero reporting the intensity map is the constant background
vector, for every epidemic incidence vector. -/
lemma intensityAt_zero {n : ℕ} (background incidence : Fin n → ℝ≥0) :
    intensityAt 0 zero_le_one background incidence = background := by
  funext j
  simp [intensityAt]

/-- The independent Poisson reporting law on a finite interval
index, as a kernel from the intensity vector. -/
noncomputable def reportingLaw {n : ℕ} :
    ProbabilityTheory.Kernel (Fin n → ℝ≥0) (Fin n → ℕ) :=
  ProbabilityTheory.piPoissonKernel (Fin n)

/-- **The reporting law determines its intensities.** The
independent Poisson reporting law is injective: equal reporting
laws come only from equal intensity vectors. -/
lemma reportingLaw_injective {n : ℕ} :
    Function.Injective (reportingLaw (n := n)) :=
  ProbabilityTheory.piPoissonKernel_injective

/-- **Nonidentification at zero reporting.** With at least one interval
(`n ≠ 0`), compose the reporting law with the intensity map at `rho = 0`. The resulting
law family is constant in the epidemic incidence vector (every
incidence has the same background-only intensity, by
`intensityAt_zero`), while the estimand `incidence 0` varies: the
zero vector and the vector differing only at coordinate `0` have
the same reporting law but estimands `0` and `1`. Hence the
estimand is not identified by the zero-reporting law. -/
lemma epi_nonidentified_at_zero_reporting {n : ℕ} [NeZero n]
    (background : Fin n → ℝ≥0) :
    ¬ MathlibExt.Probability.Statistics.IsIdentifiedBy
      (fun incidence : Fin n → ℝ≥0 =>
        reportingLaw (intensityAt 0 zero_le_one background incidence))
      (fun incidence : Fin n → ℝ≥0 => (incidence 0 : ℝ)) := by
  apply MathlibExt.Probability.Statistics.not_isIdentifiedBy_of_eq_of_ne
    (θ := fun _ => (0 : ℝ≥0)) (θ' := fun i => if i = 0 then 1 else 0)
  · rw [intensityAt_zero, intensityAt_zero]
  · simp

end MathlibExt.Biology.Epidemiology.IncidenceObservation.Law
