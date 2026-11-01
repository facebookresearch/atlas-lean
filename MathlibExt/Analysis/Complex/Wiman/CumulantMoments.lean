/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.CoefficientExponentialFamily

@[expose] public section

namespace Complex

open MeasureTheory ProbabilityTheory

noncomputable section

/-- **The logarithmic majorant is $C^2$.** Let $f$ be an entire function with Taylor
coefficients $a_n$ at the origin, and let $\Phi(x) = \log \sum_{n \ge 0} |a_n| e^{nx}$ be the
logarithm of its radial Taylor majorant at radius $e^x$ (with $\log 0 = 0$). Then $\Phi$ is
twice continuously differentiable on $\mathbb{R}$. -/
theorem contDiff_two_wimanGrowth
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    ContDiff ℝ 2 (wimanGrowth f) := by
  have hcgf :
      ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
          (wimanCoefficientMeasure f) = wimanGrowth f := by
    funext x
    exact wiman_cgf_eq_growth f hf x
  rw [← hcgf]
  have hAnalytic :
      AnalyticOnNhd ℝ
        (ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
          (wimanCoefficientMeasure f)) Set.univ := by
    simpa [integrableExpSet_wimanCoefficientMeasure_eq_univ f hf] using
      (ProbabilityTheory.analyticOnNhd_cgf
        (X := fun n : ℕ => (n : ℝ)) (μ := wimanCoefficientMeasure f))
  exact hAnalytic.contDiff

/-- **Derivative of the logarithmic majorant as a mean.** Let $f$ be an entire function whose
Taylor coefficients $a_n$ at the origin are not all zero, and let
$\Phi(x) = \log \sum_{n \ge 0} |a_n| e^{nx}$. For real $x$, let $\nu_x$ be the coefficient
measure tilted at $x$, the probability measure on $\mathbb{N}$ with
$\nu_x(\{n\}) = |a_n| e^{nx} / \sum_{m \ge 0} |a_m| e^{mx}$. Then
$\Phi'(x) = \int n \, d\nu_x(n)$, the mean of $n$ under $\nu_x$. -/
theorem deriv_wimanGrowth_eq_expectation
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (_hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) (x : ℝ) :
    deriv (wimanGrowth f) x =
      ∫ n : ℕ, (n : ℝ) ∂(wimanTiltedMeasure f x) := by
  have hcgf :
      ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
          (wimanCoefficientMeasure f) = wimanGrowth f := by
    funext y
    exact wiman_cgf_eq_growth f hf y
  rw [← hcgf]
  simpa only [wimanTiltedMeasure] using
    (ProbabilityTheory.integral_tilted_mul_self
      (X := fun n : ℕ => (n : ℝ)) (μ := wimanCoefficientMeasure f) (t := x)
      (mem_interior_integrableExpSet_wimanCoefficientMeasure f hf x)).symm

/-- **Second derivative of the logarithmic majorant as a variance.** Let $f$ be an entire
function whose Taylor coefficients $a_n$ at the origin are not all zero, and let
$\Phi(x) = \log \sum_{n \ge 0} |a_n| e^{nx}$. For real $x$, let $\nu_x$ be the coefficient
measure tilted at $x$, the probability measure on $\mathbb{N}$ with
$\nu_x(\{n\}) = |a_n| e^{nx} / \sum_{m \ge 0} |a_m| e^{mx}$. Then $\Phi''(x)$ is the variance
of $n$ under $\nu_x$. -/
theorem iteratedDeriv_two_wimanGrowth_eq_variance
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (_hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) (x : ℝ) :
    iteratedDeriv 2 (wimanGrowth f) x =
      ProbabilityTheory.variance
        (fun n : ℕ => (n : ℝ)) (wimanTiltedMeasure f x) := by
  have hcgf :
      ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
          (wimanCoefficientMeasure f) = wimanGrowth f := by
    funext y
    exact wiman_cgf_eq_growth f hf y
  rw [← hcgf]
  simpa only [wimanTiltedMeasure] using
    (ProbabilityTheory.variance_tilted_mul
      (X := fun n : ℕ => (n : ℝ)) (μ := wimanCoefficientMeasure f) (t := x)
      (mem_interior_integrableExpSet_wimanCoefficientMeasure f hf x)).symm

/-- **The logarithmic majorant has nonnegative second derivative.** Let $f$ be an entire
function whose Taylor coefficients $a_n$ at the origin are not all zero, and let
$\Phi(x) = \log \sum_{n \ge 0} |a_n| e^{nx}$. Then $\Phi''(x) \ge 0$ for every real $x$. -/
theorem iteratedDeriv_two_wimanGrowth_nonneg
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) (x : ℝ) :
    0 ≤ iteratedDeriv 2 (wimanGrowth f) x := by
  rw [iteratedDeriv_two_wimanGrowth_eq_variance f hf hne x]
  exact ProbabilityTheory.variance_nonneg _ _

end

end Complex
