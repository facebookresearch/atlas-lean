/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import MathlibExt.Probability.Statistics.SteinLemma

/-!
# Tweedie's formula for Gaussian location mixtures

Let a parameter `μ` be drawn from a prior `g` (any finite nonzero measure on `ℝ`, atoms allowed)
and, given `μ`, let `x ~ N(μ, v)` with known variance `v > 0`. The marginal density of `x` is
`f(x) = ∫ φ_v(x - μ) g(dμ)` and Bayes' rule gives the posterior mean
`E[μ | x] = ∫ μ φ_v(x - μ) g(dμ) / f(x)`.

**Tweedie's formula** (Robbins 1956, crediting M. K. Tweedie; Efron 2011, equation (1.4)) says
that this posterior mean is `x + v (log f)'(x)`: the unbiased estimate `x` plus a Bayes
correction that only involves the marginal density `f`, never the prior itself.

## Main results

* `gaussianMixtureDensity`, `gaussianPosteriorMean`, `gaussianPosteriorSecondMoment`: the marginal
  density and the Bayes posterior moments.
* `hasDerivAt_gaussianMixtureDensity`: `f` is differentiable everywhere, with
  `f'(x) = ∫ (μ - x) / v φ_v(x - μ) g(dμ)` (differentiation under the integral sign).
* `gaussianMixtureDensity_pos`: `f > 0`.
* `gaussianPosteriorMean_eq_add_mul_deriv_log`: Tweedie's formula `E[μ | x] = x + v (log f)'(x)`.
* `gaussianPosteriorSecondMoment_sub_sq_eq`: `Var(μ | x) = v (1 + v (log f)''(x))`.
* `gaussianLocationJoint`, `gaussianLocationJoint_prod_apply`: the joint law of `(μ, x)`.
* `condExp_fst_gaussianLocationJoint`: for a prior with a finite first moment, the Bayes ratio is
  a version of the conditional expectation `E[μ | x]` under the joint law.
* `gaussianPosteriorMean_gaussianReal`: for the prior `N(0, A)`, `E[μ | x] = A / (A + v) x`
  (the normal–normal Bayes rule behind the James–Stein estimator), proved with Stein's lemma.

## References

* H. Robbins, *An empirical Bayes approach to statistics*, Proc. Third Berkeley Symp. Math.
  Statist. Probab., Vol. 1, Univ. California Press (1956), 157–163.
* B. Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011),
  1602–1614, equations (1.2)–(1.4) and (2.8) (equation numbers from the author's manuscript
  posted on his Stanford page).
* B. Efron, *Empirical Bayes: Concepts and Methods*, manuscript (2021), equations (3.9)–(3.10)
  and (3.22)–(3.25).
* I. M. Johnstone, *Gaussian estimation: Sequence and wavelet models*, draft of 16 September
  2019, equation (2.26).
-/

@[expose] public section

open MeasureTheory Real Metric
open scoped NNReal

namespace ProbabilityTheory

/-- **Marginal density of a Gaussian location mixture.** For a prior `g` on the mean and a
variance `v > 0`, the Bochner integral `f(x) = ∫ φ_v(x - μ) g(dμ)`. For a finite prior it is the
density of `x` when `μ ~ g` and `x | μ ~ N(μ, v)` (for a finite prior that is not a probability
measure, the unnormalised density, of mass `g univ`); for any prior it is that density at every
`x` where `μ ↦ φ_v(x - μ)` is `g`-integrable. Where the integrand is not integrable the Bochner
integral is `0`, which is not a density value: for `g = ∞ • δ₃` the value is `0` at every `x`.
For `v = 0`, which is excluded, `gaussianPDFReal μ 0` vanishes identically (while
`gaussianReal μ 0 = δ_μ`), so the value would be `0`. -/
noncomputable def gaussianMixtureDensity (g : Measure ℝ) (v : ℝ≥0) [NeZero v] (x : ℝ) : ℝ :=
  ∫ μ, gaussianPDFReal μ v x ∂g

/-- **Posterior mean in the Gaussian location model.** Bayes' rule for `μ ~ g` and
`x | μ ~ N(μ, v)` with `v > 0`: `E[μ | x] = ∫ μ φ_v(x - μ) g(dμ) / f(x)`, with `f` the marginal
density. It is the posterior mean at `x` when both integrands are `g`-integrable and the
normaliser `f(x)` is positive and finite, which holds for every finite nonzero prior. Otherwise
the Bochner integrals are totalised and the value is `0` (for `g = ∞ • δ₃` at every `x`), not a
posterior mean. For `v = 0`, which is excluded, the Gaussian density vanishes identically and the
value would be `0` instead of `x`. -/
noncomputable def gaussianPosteriorMean (g : Measure ℝ) (v : ℝ≥0) [NeZero v] (x : ℝ) : ℝ :=
  (∫ μ, μ * gaussianPDFReal μ v x ∂g) / gaussianMixtureDensity g v x

private lemma hasDerivAt_gaussianPDFReal_param (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) :
    HasDerivAt (fun y => gaussianPDFReal μ v y) ((μ - y) / v * gaussianPDFReal μ v y) y := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h := (((hasDerivAt_id y).sub_const μ).pow 2).neg.div_const (2 * (v : ℝ))
  have he := h.exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  convert he using 1
  · ext y
    rfl
  · simp only [gaussianPDFReal, Pi.pow_apply, Pi.neg_apply, id_eq, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one, mul_one]
    field_simp
    ring

private lemma abs_mul_exp_le {v : ℝ} (hv : 0 < v) (t : ℝ) :
    |t| * rexp (-t ^ 2 / (2 * v)) ≤ v + 1 := by
  have h1 : 1 + t ^ 2 / (2 * v) ≤ rexp (t ^ 2 / (2 * v)) := by
    have := Real.add_one_le_exp (t ^ 2 / (2 * v)); linarith
  have h2 : |t| ≤ (v + 1) * (1 + t ^ 2 / (2 * v)) := by
    have ht : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [← sub_nonneg, ht]
    have : (v + 1) * (1 + |t| ^ 2 / (2 * v)) - |t| =
        ((v + 1) * |t| ^ 2 - 2 * v * |t| + 2 * v * (v + 1)) / (2 * v) := by
      field_simp
      ring
    rw [this]
    apply div_nonneg _ (by positivity)
    nlinarith [sq_nonneg (|t| - v), abs_nonneg t, sq_nonneg |t|]
  have hexp : rexp (-t ^ 2 / (2 * v)) * rexp (t ^ 2 / (2 * v)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hpos := Real.exp_pos (-t ^ 2 / (2 * v))
  calc |t| * rexp (-t ^ 2 / (2 * v))
      ≤ (v + 1) * (1 + t ^ 2 / (2 * v)) * rexp (-t ^ 2 / (2 * v)) :=
        mul_le_mul_of_nonneg_right h2 hpos.le
    _ ≤ (v + 1) * rexp (t ^ 2 / (2 * v)) * rexp (-t ^ 2 / (2 * v)) := by
        gcongr
    _ = v + 1 := by rw [mul_assoc, mul_comm (rexp _), hexp, mul_one]

private lemma gaussianPDFReal_le (μ : ℝ) (v : ℝ≥0) (y : ℝ) :
    gaussianPDFReal μ v y ≤ (√(2 * π * v))⁻¹ := by
  rw [gaussianPDFReal]
  have : rexp (-(y - μ) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  calc (√(2 * π * v))⁻¹ * rexp (-(y - μ) ^ 2 / (2 * v)) ≤ (√(2 * π * v))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

private lemma abs_sub_mul_gaussianPDFReal_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) :
    |μ - y| * gaussianPDFReal μ v y ≤ (v + 1) * (√(2 * π * v))⁻¹ := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h := abs_mul_exp_le hvpos (y - μ)
  rw [abs_sub_comm] at h
  rw [gaussianPDFReal, mul_left_comm]
  calc (√(2 * π * v))⁻¹ * (|μ - y| * rexp (-(y - μ) ^ 2 / (2 * v)))
      ≤ (√(2 * π * v))⁻¹ * (v + 1) := by gcongr
    _ = _ := mul_comm _ _

private lemma integrable_gaussianPDFReal_param (g : Measure ℝ) [IsFiniteMeasure g] (v : ℝ≥0)
    (x : ℝ) : Integrable (fun μ => gaussianPDFReal μ v x) g := by
  refine (integrable_const (√(2 * π * v))⁻¹).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun μ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact gaussianPDFReal_le μ v x

private lemma integrable_sub_mul_gaussianPDFReal_param (g : Measure ℝ) [IsFiniteMeasure g]
    {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Integrable (fun μ => (μ - x) * gaussianPDFReal μ v x) g := by
  refine (integrable_const ((v + 1) * (√(2 * π * v))⁻¹)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun μ => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact abs_sub_mul_gaussianPDFReal_le μ hv x

private lemma integrable_mul_gaussianPDFReal_param (g : Measure ℝ) [IsFiniteMeasure g]
    {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Integrable (fun μ => μ * gaussianPDFReal μ v x) g := by
  have h := (integrable_sub_mul_gaussianPDFReal_param g hv x).add
    ((integrable_gaussianPDFReal_param g v x).const_mul x)
  refine h.congr (Filter.Eventually.of_forall fun μ => ?_)
  simp only [Pi.add_apply]
  ring

/-- **The marginal density of a Gaussian location mixture is differentiable.** For a finite
prior `g` and `v > 0`, `f(x) = ∫ φ_v(x - μ) g(dμ)` has derivative
`f'(x) = ∫ (μ - x) / v φ_v(x - μ) g(dμ)` at every `x` (differentiation under the integral sign,
dominated by a constant since `|t| exp(-t² / 2v)` is bounded). -/
theorem hasDerivAt_gaussianMixtureDensity (g : Measure ℝ) [IsFiniteMeasure g] {v : ℝ≥0}
    [NeZero v] (x : ℝ) :
    HasDerivAt (gaussianMixtureDensity g v)
      (∫ μ, (μ - x) / v * gaussianPDFReal μ v x ∂g) x := by
  have hv : v ≠ 0 := NeZero.ne v
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := g) (x₀ := x)
    (F := fun y μ => gaussianPDFReal μ v y)
    (F' := fun y μ => (μ - y) / v * gaussianPDFReal μ v y)
    (bound := fun _ => (v + 1) * (√(2 * π * v))⁻¹ / v) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun y => (by fun_prop))
    (integrable_gaussianPDFReal_param g v x) (by fun_prop)
    (Filter.Eventually.of_forall fun μ y _ => by
      have h := abs_sub_mul_gaussianPDFReal_le μ hv y
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hvpos,
        abs_of_nonneg (gaussianPDFReal_nonneg _ _ _), div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right h hvpos.le)
    (integrable_const _)
    (Filter.Eventually.of_forall fun μ y _ => hasDerivAt_gaussianPDFReal_param μ hv y)
  exact key.2

/-- **The marginal density of a Gaussian location mixture is positive.** For a finite nonzero
prior `g` and `v > 0`, `f(x) > 0` at every `x`. -/
theorem gaussianMixtureDensity_pos (g : Measure ℝ) [IsFiniteMeasure g] [NeZero g] {v : ℝ≥0}
    [NeZero v] (x : ℝ) : 0 < gaussianMixtureDensity g v x := by
  have hv : v ≠ 0 := NeZero.ne v
  rw [gaussianMixtureDensity, integral_pos_iff_support_of_nonneg
    (fun μ => gaussianPDFReal_nonneg μ v x) (integrable_gaussianPDFReal_param g v x)]
  have : Function.support (fun μ => gaussianPDFReal μ v x) = Set.univ :=
    Set.eq_univ_of_forall fun μ => (gaussianPDFReal_pos μ v x hv).ne'
  rw [this, pos_iff_ne_zero, Ne, Measure.measure_univ_eq_zero]
  exact NeZero.ne g

/-- **Tweedie's formula.** Let `μ ~ g`, a finite nonzero prior on `ℝ` (atoms allowed, no moment
assumption), and `x | μ ~ N(μ, v)` with `v > 0`; let `f` be the marginal density of `x`. Then the
posterior mean is `E[μ | x] = x + v (log f)'(x)` for every `x` (Efron 2011, equation (1.4) with
`σ² = v`; Robbins 1956). Here `E[μ | x]` is the Bayes ratio `gaussianPosteriorMean`. -/
theorem gaussianPosteriorMean_eq_add_mul_deriv_log (g : Measure ℝ) [IsFiniteMeasure g] [NeZero g]
    {v : ℝ≥0} [NeZero v] (x : ℝ) :
    gaussianPosteriorMean g v x =
      x + v * deriv (fun y => Real.log (gaussianMixtureDensity g v y)) x := by
  have hv : v ≠ 0 := NeZero.ne v
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hf := gaussianMixtureDensity_pos g (v := v) x
  rw [((hasDerivAt_gaussianMixtureDensity g (v := v) x).log hf.ne').deriv, gaussianPosteriorMean]
  have hsplit : ∫ μ, (μ - x) / v * gaussianPDFReal μ v x ∂g =
      ((∫ μ, μ * gaussianPDFReal μ v x ∂g) - x * gaussianMixtureDensity g v x) / v := by
    rw [gaussianMixtureDensity, ← integral_const_mul,
      ← integral_sub (integrable_mul_gaussianPDFReal_param g hv x)
        ((integrable_gaussianPDFReal_param g v x).const_mul x), ← integral_div]
    congr 1
    ext μ
    ring
  rw [hsplit]
  field_simp
  ring

/-! ### The second-order formula: posterior variance -/

/-- **Posterior second moment in the Gaussian location model.** Bayes' rule for `μ ~ g` and
`x | μ ~ N(μ, v)` with `v > 0`: `E[μ² | x] = ∫ μ² φ_v(x - μ) g(dμ) / f(x)`. As for
`gaussianPosteriorMean`, it is the posterior second moment when both integrands are
`g`-integrable and `f(x)` is positive and finite (every finite nonzero prior); otherwise the value
is the totalised `0` (for `g = ∞ • δ₃` at every `x`). For `v = 0`, which is excluded, the value
would be `0` instead of `x²`. -/
noncomputable def gaussianPosteriorSecondMoment (g : Measure ℝ) (v : ℝ≥0) [NeZero v] (x : ℝ) :
    ℝ :=
  (∫ μ, μ ^ 2 * gaussianPDFReal μ v x ∂g) / gaussianMixtureDensity g v x

private lemma sq_mul_exp_le {v : ℝ} (hv : 0 < v) (t : ℝ) :
    t ^ 2 * rexp (-t ^ 2 / (2 * v)) ≤ 2 * v := by
  have h1 : t ^ 2 / (2 * v) ≤ rexp (t ^ 2 / (2 * v)) := by
    have := Real.add_one_le_exp (t ^ 2 / (2 * v)); linarith
  have hexp : rexp (-t ^ 2 / (2 * v)) * rexp (t ^ 2 / (2 * v)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hpos := Real.exp_pos (-t ^ 2 / (2 * v))
  have h2 : t ^ 2 = 2 * v * (t ^ 2 / (2 * v)) := by field_simp
  calc t ^ 2 * rexp (-t ^ 2 / (2 * v))
      = 2 * v * (t ^ 2 / (2 * v)) * rexp (-t ^ 2 / (2 * v)) := by rw [← h2]
    _ ≤ 2 * v * rexp (t ^ 2 / (2 * v)) * rexp (-t ^ 2 / (2 * v)) := by gcongr
    _ = 2 * v := by rw [mul_assoc, mul_comm (rexp _), hexp, mul_one]

private lemma sq_sub_mul_gaussianPDFReal_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) :
    (μ - y) ^ 2 * gaussianPDFReal μ v y ≤ 2 * v * (√(2 * π * v))⁻¹ := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h := sq_mul_exp_le hvpos (y - μ)
  rw [gaussianPDFReal, mul_left_comm, show (μ - y) ^ 2 = (y - μ) ^ 2 by ring]
  calc (√(2 * π * v))⁻¹ * ((y - μ) ^ 2 * rexp (-(y - μ) ^ 2 / (2 * v)))
      ≤ (√(2 * π * v))⁻¹ * (2 * v) := by gcongr
    _ = _ := mul_comm _ _

private lemma integrable_sq_sub_mul_gaussianPDFReal_param (g : Measure ℝ) [IsFiniteMeasure g]
    {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Integrable (fun μ => (μ - x) ^ 2 * gaussianPDFReal μ v x) g := by
  refine (integrable_const (2 * v * (√(2 * π * v))⁻¹)).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun μ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg _ _ _))]
    exact sq_sub_mul_gaussianPDFReal_le μ hv x

private lemma integrable_sq_mul_gaussianPDFReal_param (g : Measure ℝ) [IsFiniteMeasure g]
    {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Integrable (fun μ => μ ^ 2 * gaussianPDFReal μ v x) g := by
  have h := ((integrable_sq_sub_mul_gaussianPDFReal_param g hv x).add
    ((integrable_mul_gaussianPDFReal_param g hv x).const_mul (2 * x))).sub
    ((integrable_gaussianPDFReal_param g v x).const_mul (x ^ 2))
  refine h.congr (Filter.Eventually.of_forall fun μ => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

private lemma hasDerivAt_gaussianMixtureDensity_deriv (g : Measure ℝ) [IsFiniteMeasure g]
    {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => ∫ μ, (μ - y) / v * gaussianPDFReal μ v y ∂g)
      (∫ μ, ((μ - x) ^ 2 / v ^ 2 - 1 / v) * gaussianPDFReal μ v x ∂g) x := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := g) (x₀ := x)
    (F := fun y μ => (μ - y) / v * gaussianPDFReal μ v y)
    (F' := fun y μ => ((μ - y) ^ 2 / v ^ 2 - 1 / v) * gaussianPDFReal μ v y)
    (bound := fun _ => (2 * v * (√(2 * π * v))⁻¹) / v ^ 2 + (√(2 * π * v))⁻¹ / v)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun y => (by fun_prop))
    ((integrable_sub_mul_gaussianPDFReal_param g hv x).div_const (v : ℝ) |>.congr
      (Filter.Eventually.of_forall fun μ =>
        show (μ - x) * gaussianPDFReal μ v x / v = (μ - x) / v * gaussianPDFReal μ v x by ring))
    (by fun_prop)
    (Filter.Eventually.of_forall fun μ y _ => by
      have h1 := sq_sub_mul_gaussianPDFReal_le μ hv y
      have h2 := gaussianPDFReal_le μ v y
      have h0 := gaussianPDFReal_nonneg μ v y
      rw [Real.norm_eq_abs, sub_mul]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_mul_eq_mul_div,
        div_mul_eq_mul_div, one_mul]
      gcongr)
    (integrable_const _)
    (Filter.Eventually.of_forall fun μ y _ => by
      have h1 : HasDerivAt (fun y : ℝ => (μ - y) / v) (-1 / v) y := by
        simpa using ((hasDerivAt_id y).const_sub μ).div_const (v : ℝ)
      have h := h1.mul (hasDerivAt_gaussianPDFReal_param μ hv y)
      convert h using 1
      ring)
  exact key.2

/-- **Tweedie's formula for the posterior variance.** Under the hypotheses of Tweedie's formula,
`Var(μ | x) = E[μ² | x] - E[μ | x]² = v (1 + v (log f)''(x))` for every `x` (Efron 2011,
equation (2.8), second component, with `σ² = v`). -/
theorem gaussianPosteriorSecondMoment_sub_sq_eq (g : Measure ℝ) [IsFiniteMeasure g] [NeZero g]
    {v : ℝ≥0} [NeZero v] (x : ℝ) :
    gaussianPosteriorSecondMoment g v x - gaussianPosteriorMean g v x ^ 2 =
      v * (1 + v * deriv (deriv fun y => Real.log (gaussianMixtureDensity g v y)) x) := by
  have hv : v ≠ 0 := NeZero.ne v
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  set f := gaussianMixtureDensity g v
  set F1 : ℝ → ℝ := fun y => ∫ μ, (μ - y) / v * gaussianPDFReal μ v y ∂g
  have hd1 : deriv (fun y => Real.log (f y)) = fun y => F1 y / f y := by
    ext y
    exact ((hasDerivAt_gaussianMixtureDensity g (v := v) y).log
      (gaussianMixtureDensity_pos g (v := v) y).ne').deriv
  have hq : HasDerivAt (fun y => F1 y / f y) _ x :=
    (hasDerivAt_gaussianMixtureDensity_deriv g hv x).div
      (hasDerivAt_gaussianMixtureDensity g (v := v) x) (gaussianMixtureDensity_pos g (v := v) x).ne'
  rw [hd1, hq.deriv]
  set N0 := f x
  set N1 := ∫ μ, μ * gaussianPDFReal μ v x ∂g
  set N2 := ∫ μ, μ ^ 2 * gaussianPDFReal μ v x ∂g
  have i0 := integrable_gaussianPDFReal_param g v x
  have i1 := integrable_mul_gaussianPDFReal_param g hv x
  have i2 := integrable_sq_mul_gaussianPDFReal_param g hv x
  have hF1 : ∫ μ, (μ - x) / v * gaussianPDFReal μ v x ∂g = (N1 - x * N0) / v := by
    simp only [N0, N1, f, gaussianMixtureDensity]
    rw [← integral_const_mul, ← integral_sub i1 (i0.const_mul x), ← integral_div]
    congr 1; ext μ; ring
  have hF2 : ∫ μ, ((μ - x) ^ 2 / v ^ 2 - 1 / v) * gaussianPDFReal μ v x ∂g =
      (N2 - 2 * x * N1 + x ^ 2 * N0) / v ^ 2 - N0 / v := by
    have he : (fun μ => ((μ - x) ^ 2 / v ^ 2 - 1 / v) * gaussianPDFReal μ v x) =
        fun μ => (1 / (v : ℝ) ^ 2) * (μ ^ 2 * gaussianPDFReal μ v x) -
          (2 * x / (v : ℝ) ^ 2) * (μ * gaussianPDFReal μ v x) +
          (x ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal μ v x := by
      ext μ; ring
    have i3 : Integrable (fun μ => (1 / (v : ℝ) ^ 2) * (μ ^ 2 * gaussianPDFReal μ v x) -
        (2 * x / (v : ℝ) ^ 2) * (μ * gaussianPDFReal μ v x)) g :=
      (i2.const_mul _).sub (i1.const_mul _)
    rw [he, integral_add i3 (i0.const_mul _),
      integral_sub (i2.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul]
    simp only [N0, N1, N2, f, gaussianMixtureDensity]
    ring
  have hN0 : 0 < N0 := gaussianMixtureDensity_pos g (v := v) x
  rw [hF1, hF2, gaussianPosteriorSecondMoment, gaussianPosteriorMean]
  change N2 / N0 - (N1 / N0) ^ 2 = _
  field_simp
  ring

/-! ### The posterior mean as a conditional expectation -/

/-- **Joint law of a Gaussian location model.** The law on `ℝ × ℝ` of `(μ, x)` when `μ ~ g` and
`x | μ ~ N(μ, v)` with `v > 0`: the measure `g ⊗ Lebesgue` with density `φ_v(x - μ)` (for a prior
that is not a probability measure, a measure of mass `g univ`). For `v = 0`, which is excluded,
the density vanishes identically and the measure would be zero. -/
noncomputable def gaussianLocationJoint (g : Measure ℝ) (v : ℝ≥0) [NeZero v] : Measure (ℝ × ℝ) :=
  (g.prod volume).withDensity fun q => ((gaussianPDFReal q.1 v q.2).toNNReal : ENNReal)

private lemma measurable_jointDensity (v : ℝ≥0) :
    Measurable fun q : ℝ × ℝ => (gaussianPDFReal q.1 v q.2).toNNReal :=
  (measurable_uncurry_gaussianPDFReal.comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).real_toNNReal

/-- **The joint law of a Gaussian location model has the right marginal and kernel.** For
measurable `A, B` and `v > 0`, `P(μ ∈ A, x ∈ B) = ∫_A N(μ, v)(B) g(dμ)`. -/
theorem gaussianLocationJoint_prod_apply (g : Measure ℝ) [SFinite g] {v : ℝ≥0} [NeZero v]
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    gaussianLocationJoint g v (A ×ˢ B) = ∫⁻ μ in A, gaussianReal μ v B ∂g := by
  have hv : v ≠ 0 := NeZero.ne v
  rw [gaussianLocationJoint, withDensity_apply _ (hA.prod hB), ← Measure.prod_restrict,
    lintegral_prod (fun q : ℝ × ℝ => ((gaussianPDFReal q.1 v q.2).toNNReal : ENNReal))
      (measurable_jointDensity v).coe_nnreal_ennreal.aemeasurable]
  refine lintegral_congr fun μ => ?_
  rw [gaussianReal_apply μ hv B]
  rfl

instance (g : Measure ℝ) [IsProbabilityMeasure g] {v : ℝ≥0} [NeZero v] :
    IsProbabilityMeasure (gaussianLocationJoint g v) := by
  constructor
  rw [← Set.univ_prod_univ, gaussianLocationJoint_prod_apply g MeasurableSet.univ
    MeasurableSet.univ]
  simp

private lemma stronglyMeasurable_jointPDF (v : ℝ≥0) :
    StronglyMeasurable fun q : ℝ × ℝ => gaussianPDFReal q.1 v q.2 :=
  (measurable_uncurry_gaussianPDFReal.comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).stronglyMeasurable

private lemma measurable_gaussianMixtureDensity (g : Measure ℝ) [SFinite g] (v : ℝ≥0)
    [NeZero v] :
    Measurable (gaussianMixtureDensity g v) := by
  have h : StronglyMeasurable fun q : ℝ × ℝ => gaussianPDFReal q.2 v q.1 :=
    (measurable_uncurry_gaussianPDFReal.comp
      (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := g)).measurable

private lemma measurable_gaussianPosteriorMean (g : Measure ℝ) [SFinite g] (v : ℝ≥0)
    [NeZero v] :
    Measurable (gaussianPosteriorMean g v) := by
  have h : StronglyMeasurable fun q : ℝ × ℝ => q.2 * gaussianPDFReal q.2 v q.1 :=
    (measurable_snd.mul (measurable_uncurry_gaussianPDFReal.comp
      (measurable_snd.prodMk (measurable_const.prodMk measurable_fst)))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := g)).measurable.div (measurable_gaussianMixtureDensity g v)

private lemma integrable_fst_mul_jointPDF (g : Measure ℝ) [IsFiniteMeasure g]
    (hg : Integrable id g) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun q : ℝ × ℝ => gaussianPDFReal q.1 v q.2 * q.1) (g.prod volume) := by
  have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => gaussianPDFReal q.1 v q.2 * q.1)
      (g.prod volume) :=
    ((stronglyMeasurable_jointPDF v).mul measurable_fst.stronglyMeasurable).aestronglyMeasurable
  refine (integrable_prod_iff hm).2 ⟨Filter.Eventually.of_forall fun μ => ?_, ?_⟩
  · exact (integrable_gaussianPDFReal μ v).mul_const μ
  · refine (hg.norm).congr (Filter.Eventually.of_forall fun μ => ?_)
    simp only [id, norm_mul, Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    rw [integral_mul_const, integral_gaussianPDFReal_eq_one μ hv, one_mul]

private lemma posteriorMean_mul_density (g : Measure ℝ) [IsFiniteMeasure g] [NeZero g]
    {v : ℝ≥0} [NeZero v] (x : ℝ) :
    gaussianPosteriorMean g v x * gaussianMixtureDensity g v x =
      ∫ μ, μ * gaussianPDFReal μ v x ∂g := by
  have hv : v ≠ 0 := NeZero.ne v
  rw [gaussianPosteriorMean, div_mul_cancel₀ _ (gaussianMixtureDensity_pos g (v := v) x).ne']

private lemma integrable_jointPDF_mul_posteriorMean (g : Measure ℝ) [IsProbabilityMeasure g]
    (hg : Integrable id g) {v : ℝ≥0} [NeZero v] :
    Integrable (fun q : ℝ × ℝ => gaussianPDFReal q.1 v q.2 * gaussianPosteriorMean g v q.2)
      (g.prod volume) := by
  have hv : v ≠ 0 := NeZero.ne v
  have hm : AEStronglyMeasurable
      (fun q : ℝ × ℝ => gaussianPDFReal q.1 v q.2 * gaussianPosteriorMean g v q.2)
      (g.prod volume) :=
    ((stronglyMeasurable_jointPDF v).mul
      ((measurable_gaussianPosteriorMean g v).comp measurable_snd).stronglyMeasurable
      ).aestronglyMeasurable
  have hH := integrable_fst_mul_jointPDF g hg hv
  have hH' := ((integrable_prod_iff' hH.aestronglyMeasurable).1 hH).2
  refine (integrable_prod_iff' hm).2 ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · simpa only using (integrable_gaussianPDFReal_param g v x).mul_const
      (gaussianPosteriorMean g v x)
  · refine hH'.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have hc : StronglyMeasurable fun q : ℝ × ℝ =>
          ‖gaussianPDFReal q.2 v q.1 * gaussianPosteriorMean g v q.1‖ :=
        ((measurable_uncurry_gaussianPDFReal.comp
          (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))).mul
          ((measurable_gaussianPosteriorMean g v).comp measurable_fst)).norm.stronglyMeasurable
      exact (hc.integral_prod_right' (ν := g)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
        integral_mul_const]
      rw [← gaussianMixtureDensity, mul_comm,
        ← abs_of_pos (gaussianMixtureDensity_pos g (v := v) x),
        ← abs_mul, posteriorMean_mul_density g (v := v) x]
      refine (abs_integral_le_integral_abs).trans_eq ?_
      congr 1
      ext μ
      rw [abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _), mul_comm]

/-- **Tweedie's formula, conditional expectation form.** Let `μ ~ g`, a probability measure on
`ℝ` with a finite first moment, and `x | μ ~ N(μ, v)` with `v > 0`. Under the joint law of
`(μ, x)`, the conditional expectation `E[μ | x]` is almost surely the Bayes ratio
`gaussianPosteriorMean g v x`, which by `gaussianPosteriorMean_eq_add_mul_deriv_log` equals
`x + v (log f)'(x)` (Efron 2011, equations (1.2)–(1.4) with `σ² = v`). -/
theorem condExp_fst_gaussianLocationJoint (g : Measure ℝ) [IsProbabilityMeasure g]
    (hg : Integrable id g) {v : ℝ≥0} [NeZero v] :
    (fun q : ℝ × ℝ => gaussianPosteriorMean g v q.2) =ᵐ[gaussianLocationJoint g v]
      (gaussianLocationJoint g v)[Prod.fst | MeasurableSpace.comap Prod.snd inferInstance] := by
  have hv : v ≠ 0 := NeZero.ne v
  set J := gaussianLocationJoint g v with hJ
  have hρ := measurable_jointDensity v
  have hm : MeasurableSpace.comap Prod.snd inferInstance ≤ (inferInstance : MeasurableSpace (ℝ × ℝ))
    := measurable_snd.comap_le
  have hH := integrable_fst_mul_jointPDF g hg hv
  have hK := integrable_jointPDF_mul_posteriorMean g hg (v := v)
  have hsmul : ∀ (F : ℝ × ℝ → ℝ) q, (gaussianPDFReal q.1 v q.2).toNNReal • F q =
      gaussianPDFReal q.1 v q.2 * F q := fun F q => by
    rw [NNReal.smul_def, Real.coe_toNNReal _ (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]
  have hint : ∀ F : ℝ × ℝ → ℝ,
      Integrable (fun q => gaussianPDFReal q.1 v q.2 * F q) (g.prod volume) → Integrable F J :=
    fun F hF => (integrable_withDensity_iff_integrable_smul hρ).2 (by simpa only [hsmul] using hF)
  have hfst : Integrable Prod.fst J := hint _ hH
  have hpm : Integrable (fun q : ℝ × ℝ => gaussianPosteriorMean g v q.2) J := hint _ hK
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfst (fun s _ _ => hpm.integrableOn)
    (fun s hs _ => ?_) ?_
  · obtain ⟨A, hA, rfl⟩ := hs
    have hA' : MeasurableSet (Prod.snd ⁻¹' A : Set (ℝ × ℝ)) := measurable_snd hA
    rw [← integral_indicator hA', ← integral_indicator hA', hJ, gaussianLocationJoint,
      integral_withDensity_eq_integral_smul hρ, integral_withDensity_eq_integral_smul hρ]
    simp only [hsmul]
    have hind : ∀ F : ℝ × ℝ → ℝ, (fun q : ℝ × ℝ =>
        gaussianPDFReal q.1 v q.2 * (Prod.snd ⁻¹' A).indicator F q) =
          (Prod.snd ⁻¹' A).indicator (fun q => gaussianPDFReal q.1 v q.2 * F q) := fun F => by
      ext q
      exact (Set.indicator_mul_right (Prod.snd ⁻¹' A)
        (fun q : ℝ × ℝ => gaussianPDFReal q.1 v q.2) F).symm
    rw [hind, hind, integral_prod_symm _ (hK.indicator hA'),
      integral_prod_symm _ (hH.indicator hA')]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ A
    · simp only [Set.indicator, Set.mem_preimage, hx, ite_true]
      rw [integral_mul_const, ← gaussianMixtureDensity, mul_comm,
        posteriorMean_mul_density g (v := v) x]
      exact integral_congr_ae (Filter.Eventually.of_forall fun μ => mul_comm _ _)
    · simp [Set.indicator, hx]
  · exact ((measurable_gaussianPosteriorMean g v).comp
      (comap_measurable Prod.snd)).aestronglyMeasurable

/-! ### The normal–normal model -/

private lemma gaussianPDFReal_comm (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x = gaussianPDFReal x v μ := by
  simp only [gaussianPDFReal, neg_sub, sub_sq', mul_comm]
  ring_nf

/-- **Posterior mean in the normal–normal model.** For the prior `μ ~ N(0, A)` and
`x | μ ~ N(μ, v)` with `v > 0`, the posterior mean is `E[μ | x] = A / (A + v) x` (B. Efron,
*Empirical Bayes: Concepts and Methods*, 2021 manuscript, equation (3.10) with `M = 0` and
`σ₀² = v`). With `v = 1` and `V = A + 1` this is the Bayes rule `(1 - 1/V) x` that the James–Stein
estimator imitates (Efron 2011, equations (3.7)–(3.8)). The proof applies Stein's lemma to the
prior: `∫ μ φ_v(x - μ) N(0, A)(dμ) = A ∫ (x - μ) / v φ_v(x - μ) N(0, A)(dμ)`. -/
theorem gaussianPosteriorMean_gaussianReal (A : ℝ≥0) {v : ℝ≥0} [NeZero v] (x : ℝ) :
    gaussianPosteriorMean (gaussianReal 0 A) v x = A / (A + v) * x := by
  have hv : v ≠ 0 := NeZero.ne v
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  set g := gaussianReal 0 A
  have hd : ∀ μ, HasDerivAt (fun μ => gaussianPDFReal μ v x)
      ((x - μ) / v * gaussianPDFReal μ v x) μ := fun μ => by
    have h := hasDerivAt_gaussianPDFReal_param x hv μ
    have e : (fun y => gaussianPDFReal x v y) = fun y => gaussianPDFReal y v x :=
      funext fun y => gaussianPDFReal_comm x v y
    rwa [e, gaussianPDFReal_comm x v μ] at h
  have hst := integrable_and_integral_sub_mul_gaussianReal 0 A (hd)
    (by
      have := (integrable_sub_mul_gaussianPDFReal_param g hv x).div_const (v : ℝ)
      refine (this.neg).congr (Filter.Eventually.of_forall fun μ => ?_)
      simp only [Pi.neg_apply]
      ring)
  have hN : ∫ μ, (x - μ) / v * gaussianPDFReal μ v x ∂g =
      (x * gaussianMixtureDensity g v x - ∫ μ, μ * gaussianPDFReal μ v x ∂g) / v := by
    rw [gaussianMixtureDensity, ← integral_const_mul,
      ← integral_sub ((integrable_gaussianPDFReal_param g v x).const_mul x)
        (integrable_mul_gaussianPDFReal_param g hv x), ← integral_div]
    congr 1
    ext μ
    ring
  rw [hN] at hst
  have hf := gaussianMixtureDensity_pos g (v := v) x
  rw [gaussianPosteriorMean, div_eq_iff hf.ne']
  have hAv : (0 : ℝ) < A + v := by positivity
  have h1 : (∫ μ, μ * gaussianPDFReal μ v x ∂g) * v =
      A * (x * gaussianMixtureDensity g v x - ∫ μ, μ * gaussianPDFReal μ v x ∂g) := by
    have h2 := hst.2
    simp only [sub_zero] at h2
    rw [mul_div_assoc'] at h2
    have h3 := congrArg (· * (v : ℝ)) h2
    simp only [div_mul_cancel₀ _ hvpos.ne'] at h3
    exact h3
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hAv.ne']
  linarith

end ProbabilityTheory
