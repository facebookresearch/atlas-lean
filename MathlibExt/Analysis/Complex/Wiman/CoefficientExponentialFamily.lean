/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.RadialMajorant
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Moments.Tilted

@[expose] public section

namespace Complex

open MeasureTheory ProbabilityTheory

open scoped ENNReal

noncomputable section

/-- The logarithm of the radial Taylor majorant at logarithmic radius `x`. -/
def wimanGrowth (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  Real.log (wimanMajorant f (Real.exp x))

/-- **Wiman coefficient measure.** For $f : \mathbb{C} \to \mathbb{C}$ with Taylor coefficients
$a_n = f^{(n)}(0)/n!$ at $0$, the Wiman coefficient measure of $f$ is the measure
$\mu_f = \sum_{n \ge 0} |a_n|\,\delta_n$ on $\mathbb{N}$, which gives each $n$ mass $|a_n|$. -/
def wimanCoefficientMeasure (f : ℂ → ℂ) : Measure ℕ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ • Measure.dirac n

/-- **Tilted coefficient measure.** Let $f : \mathbb{C} \to \mathbb{C}$ have Taylor coefficients
$a_n = f^{(n)}(0)/n!$, and let $\mu_f$ be its coefficient measure on $\mathbb{N}$, with mass $|a_n|$
at $n$. For a real number $x$, the tilted coefficient measure $\mu_{f,x}$ is the exponential tilt of
$\mu_f$ by $n \mapsto xn$: the measure with density $e^{xn} / \int e^{xm}\,d\mu_f(m)$ with respect
to $\mu_f$. -/
def wimanTiltedMeasure (f : ℂ → ℂ) (x : ℝ) : Measure ℕ :=
  (wimanCoefficientMeasure f).tilted fun n : ℕ => x * (n : ℝ)

/-- **Point masses of the Wiman coefficient measure.** Let $f : \mathbb{C} \to \mathbb{C}$ and
$a_n = f^{(n)}(0)/n!$. For every $n \in \mathbb{N}$, the Wiman coefficient measure $\mu_f$ of $f$
gives the singleton $\{n\}$ mass $\mu_f(\{n\}) = |a_n|$. -/
@[simp]
theorem wimanCoefficientMeasure_singleton (f : ℂ → ℂ) (n : ℕ) :
    wimanCoefficientMeasure f {n} = ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ := by
  exact Measure.sum_smul_dirac_singleton

/-- **Exponential moments of the Wiman coefficient measure are finite.** Let $f$ be an entire
function and let $\mu_f$ be its Wiman coefficient measure on $\mathbb{N}$, which gives each
$n \in \mathbb{N}$ mass $|a_n|$, where $a_n = f^{(n)}(0)/n!$. For every real $x$, the function
$n \mapsto e^{xn}$ is integrable with respect to $\mu_f$. -/
theorem integrable_exp_mul_wimanCoefficientMeasure
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    Integrable (fun n : ℕ => Real.exp (x * (n : ℝ))) (wimanCoefficientMeasure f) := by
  rw [wimanCoefficientMeasure]
  refine integrable_sum_dirac (fun n => by simp) ?_
  refine (summable_wimanTerm f hf (Real.exp x)).congr fun n => ?_
  rw [wimanTerm, ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_comm x (n : ℝ), Real.exp_nat_mul,
    abs_of_nonneg (pow_nonneg (Real.exp_pos x).le n)]

/-- **The exponential-integrability set of the Wiman coefficient measure is the whole line.** Let
$f$ be an entire function and let $\mu_f$ be its Wiman coefficient measure on $\mathbb{N}$. The set
of real $t$ for which $n \mapsto e^{tn}$ is integrable with respect to $\mu_f$ is all of
$\mathbb{R}$. -/
theorem integrableExpSet_wimanCoefficientMeasure_eq_univ
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    integrableExpSet (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) = Set.univ := by
  ext x
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact integrable_exp_mul_wimanCoefficientMeasure f hf x

/-- **Every real parameter is interior to the exponential-integrability set.** Let $f$ be an
entire function and let $\mu_f$ be its Wiman coefficient measure on $\mathbb{N}$. Every real $x$
lies in the interior of the set of real $t$ for which $n \mapsto e^{tn}$ is integrable with
respect to $\mu_f$. -/
theorem mem_interior_integrableExpSet_wimanCoefficientMeasure
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    x ∈ interior (integrableExpSet (fun n : ℕ => (n : ℝ))
      (wimanCoefficientMeasure f)) := by
  simp [integrableExpSet_wimanCoefficientMeasure_eq_univ f hf]

/-- **Exponential moments of the Wiman coefficient measure equal the Wiman majorant.** Let $f$ be
an entire function with Taylor coefficients $a_n = f^{(n)}(0)/n!$ at $0$, and let $\mu_f$ be its
Wiman coefficient measure on $\mathbb{N}$. For every real $x$,
$$\int e^{xn}\,d\mu_f(n) = M_f(e^x),$$
where $M_f(r) = \sum_{n \ge 0} |a_n|\,|r|^n$ is the Wiman majorant of $f$. -/
theorem integral_exp_mul_wimanCoefficientMeasure
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    ∫ n : ℕ, Real.exp (x * (n : ℝ)) ∂(wimanCoefficientMeasure f) =
      wimanMajorant f (Real.exp x) := by
  have hInt := integrable_exp_mul_wimanCoefficientMeasure f hf x
  rw [wimanCoefficientMeasure] at hInt
  have hsum : Summable (fun n : ℕ =>
      (ENNReal.ofReal ‖wimanTaylorCoefficient f n‖).toReal *
        ‖Real.exp (x * (n : ℝ))‖) :=
    hInt.summable_of_dirac
  rw [wimanCoefficientMeasure,
    integral_sum_dirac_eq_tsum
      (f := fun n : ℕ => Real.exp (x * (n : ℝ))) (fun n => by simp) hsum,
    wimanMajorant]
  apply tsum_congr
  intro n
  rw [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul, wimanTerm,
    abs_of_pos (Real.exp_pos x), mul_comm x (n : ℝ), Real.exp_nat_mul]

/-- **Moment generating function of the coefficient measure.** Let $f$ be an entire function with
Taylor coefficients $a_n = f^{(n)}(0)/n!$, and let $\mu_f$ be its coefficient measure on
$\mathbb{N}$, which has mass $|a_n|$ at $n$. For every real $x$, the moment generating function of
$n \mapsto n$ under $\mu_f$ at $x$, namely $\int e^{xn}\,d\mu_f(n)$, equals the radial majorant
$M_f(e^x)$, where $M_f(r) = \sum_n |a_n|\,|r|^n$. -/
theorem wiman_mgf_eq_majorant
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    mgf (fun n : ℕ => (n : ℝ)) (wimanCoefficientMeasure f) x =
      wimanMajorant f (Real.exp x) := by
  rw [mgf, integral_exp_mul_wimanCoefficientMeasure f hf x]

/-- **The Wiman growth is the cumulant generating function of the coefficient measure.** Let $f$
be an entire function and let $\mu_f$ be its Wiman coefficient measure on $\mathbb{N}$. For every
real $x$, the cumulant generating function of $n \mapsto n$ under $\mu_f$ at $x$, namely
$\log \int e^{xn}\,d\mu_f(n)$, equals the Wiman growth $G_f(x) = \log M_f(e^x)$, where $M_f$ is
the Wiman majorant of $f$. -/
theorem wiman_cgf_eq_growth
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    ProbabilityTheory.cgf (fun n : ℕ => (n : ℝ))
        (wimanCoefficientMeasure f) x = wimanGrowth f x := by
  rw [cgf, wimanGrowth, wiman_mgf_eq_majorant f hf x]

/-- **A nonzero Taylor coefficient makes the Wiman coefficient measure nonzero.** Let
$f : \mathbb{C} \to \mathbb{C}$ and $a_n = f^{(n)}(0)/n!$. If $a_n \ne 0$ for some $n$, then the
Wiman coefficient measure $\mu_f$ of $f$ is not the zero measure. -/
theorem wimanCoefficientMeasure_ne_zero
    (f : ℂ → ℂ) (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) :
    wimanCoefficientMeasure f ≠ 0 := by
  obtain ⟨n, hn⟩ := hne
  have hmass : ENNReal.ofReal ‖wimanTaylorCoefficient f n‖ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hn))
  intro hzero
  apply hmass
  rw [← wimanCoefficientMeasure_singleton f n, hzero]
  simp

/-- **The Wiman tilted measure is a probability measure.** Let $f$ be an entire function such that
$f^{(n)}(0)/n! \ne 0$ for some $n$, and let $\mu_f$ be its Wiman coefficient measure on
$\mathbb{N}$. For every real $x$, the Wiman tilted measure of $f$ at $x$, which has density
$n \mapsto e^{xn} / \int e^{xm}\,d\mu_f(m)$ with respect to $\mu_f$, is a probability measure. -/
theorem isProbabilityMeasure_wimanTiltedMeasure
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∃ n, wimanTaylorCoefficient f n ≠ 0) (x : ℝ) :
    IsProbabilityMeasure (wimanTiltedMeasure f x) := by
  let _ : NeZero (wimanCoefficientMeasure f) :=
    ⟨wimanCoefficientMeasure_ne_zero f hne⟩
  exact isProbabilityMeasure_tilted (integrable_exp_mul_wimanCoefficientMeasure f hf x)

/-- **Atoms of the tilted coefficient measure.** Let $f$ be an entire function with Taylor
coefficients $a_n = f^{(n)}(0)/n!$, radial majorant $M_f(r) = \sum_n |a_n|\,|r|^n$ and Taylor terms
$T_n(r) = |a_n|\,|r|^n$. For every real $x$ and every $n \in \mathbb{N}$, the tilted coefficient
measure $\mu_{f,x}$ gives the singleton $\{n\}$ mass $T_n(e^x) / M_f(e^x)$ (with the convention
$t/0 = 0$). -/
@[simp]
theorem wimanTiltedMeasure_singleton
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) (n : ℕ) :
    wimanTiltedMeasure f x {n} =
      ENNReal.ofReal
        (wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x)) := by
  rw [wimanTiltedMeasure,
    ProbabilityTheory.tilted_mul_apply_mgf'
      (μ := wimanCoefficientMeasure f) (X := fun n : ℕ => (n : ℝ))
      (t := x) (measurableSet_singleton n),
    lintegral_singleton, wiman_mgf_eq_majorant f hf x,
    wimanCoefficientMeasure_singleton]
  have hratio :
      0 ≤ Real.exp (x * (n : ℝ)) / wimanMajorant f (Real.exp x) :=
    div_nonneg (Real.exp_pos _).le (wimanMajorant_nonneg f (Real.exp x))
  rw [← ENNReal.ofReal_mul hratio]
  congr 1
  rw [wimanTerm, abs_of_pos (Real.exp_pos x), mul_comm x (n : ℝ), Real.exp_nat_mul]
  ring

/-- **Atomic form of the tilted coefficient measure.** Let $f$ be an entire function with Taylor
coefficients $a_n = f^{(n)}(0)/n!$, radial majorant $M_f(r) = \sum_n |a_n|\,|r|^n$ and Taylor terms
$T_n(r) = |a_n|\,|r|^n$. For every real $x$, the tilted coefficient measure $\mu_{f,x}$ equals
$\sum_{n \in \mathbb{N}} \frac{T_n(e^x)}{M_f(e^x)}\,\delta_n$, the measure on $\mathbb{N}$ with mass
$T_n(e^x) / M_f(e^x)$ at each $n$ (with the convention $t/0 = 0$). -/
theorem wimanTiltedMeasure_eq_sum
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    wimanTiltedMeasure f x =
      Measure.sum fun n : ℕ =>
        ENNReal.ofReal
          (wimanTerm f (Real.exp x) n / wimanMajorant f (Real.exp x)) •
            Measure.dirac n := by
  apply Measure.ext_iff_singleton.mpr
  intro n
  rw [wimanTiltedMeasure_singleton f hf x n,
    Measure.sum_smul_dirac_singleton]

end

end Complex
