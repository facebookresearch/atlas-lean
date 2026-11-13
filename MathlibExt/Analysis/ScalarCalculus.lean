/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Scalar calculus: logarithms, powers, exponentials and Taylor bounds

Derivative, integral and Taylor-remainder contracts for exponential decay, power laws,
Gaussians and rational rates, each with an explicit domain.

## i. Overview

This module is a bridge package. It assembles Mathlib's `Real.log`, `Real.exp`, `Real.logb`,
real powers (`Real.rpow`), interval integrals and series bounds into composite statements, and
defines no new functions.

`Real.log` is total in Lean: `Real.log 0 = 0` and `Real.log x = Real.log |x|`. A logarithm
argument in a physical API is a positive dimensionless number, in practice a ratio `x / x₀` of
like quantities; an exponential argument is dimensionless (such as `-k * t`) and may have either
sign, and its value is a positive ratio. Every statement below therefore takes the positivity of
each logarithm argument as an explicit hypothesis, or derives it from a stated interval; it is
never read off the definition of `Real.log`.

Taylor truncations are inequalities with explicit constants on a stated compact interval only.
They are not equalities, not asymptotic equivalences, and nothing is asserted outside the stated
interval.

## ii. Key results

- `ScalarCalculus.hasDerivAt_expDecay` : `exp (-k * x)` has derivative `-k * exp (-k * x)`.
- `ScalarCalculus.hasDerivAt_log_expDecay` : in semi-log coordinates the decay profile
  `N₀ * exp (-k * t)`, `0 < N₀`, has constant slope `-k`.
- `ScalarCalculus.integral_expDecay` : `∫ x in 0..t, exp (-k * x) = (1 - exp (-k * t)) / k`
  for `0 < k` and every `t`.
- `ScalarCalculus.integral_expDecay_ratioTime` : the decay integral up to the time
  `-log q / k` at which the profile equals a positive ratio `q` is `(1 - q) / k`.
- `ScalarCalculus.hasDerivAt_and_integral_powerLaw` : derivative of `x ^ r` for `0 < x`, and
  integrability and `∫ x in 0..1, x ^ r = 1 / (r + 1)` for `-1 < r`.
- `ScalarCalculus.hasDerivAt_logb_powerLaw` : in base-`b` log-log coordinates the power law
  `c * (x / x₀) ^ r` has constant slope `r`.
- `ScalarCalculus.integrable_and_integral_gaussian` : for `0 < a`, integrability and
  `∫ x, exp (-a * x ^ 2) = √(π / a)`, also as an improper integral with independent endpoints.
- `ScalarCalculus.hasDerivAt_gaussian` : `exp (-a * x ^ 2)` has derivative
  `-2 * a * x * exp (-a * x ^ 2)`.
- `ScalarCalculus.integral_rationalRates` : `∫ x in 0..t, 1 / (1 + x ^ 2) = arctan t`, and
  `∫ x in 0..t, 1 / (1 + x) = log (1 + t)` for `0 < 1 + t`.
- `ScalarCalculus.abs_log_one_add_sub_linear_le` : `|log (1 + x) - x| ≤ x ^ 2` on `|x| ≤ 1 / 2`.
- `ScalarCalculus.abs_log_one_add_sub_quadratic_le` :
  `|log (1 + x) - (x - x ^ 2 / 2)| ≤ |x| ^ 3` on `|x| ≤ 1 / 2`.
- `ScalarCalculus.abs_exp_sub_linear_le` : `|exp x - (1 + x)| ≤ 3 / 4 * x ^ 2` on `|x| ≤ 1`.
- `ScalarCalculus.abs_exp_sub_quadratic_le` :
  `|exp x - (1 + x + x ^ 2 / 2)| ≤ 2 / 9 * |x| ^ 3` on `|x| ≤ 1`.

## iii. Table of contents

- A. Logarithms of positive dimensionless arguments (supporting lemmas)
- B. Exponential decay
- C. Power laws
- D. Gaussians
- E. Rational rates
- F. Taylor remainder bounds on compact intervals

## iv. References

- Mathlib `Mathlib.Analysis.SpecialFunctions.Log.Basic` and
  `Mathlib.Analysis.SpecialFunctions.Log.Base`: `Real.exp_log`, `Real.log_exp`, `Real.log_mul`,
  `Real.log_div`, `Real.log_div_log`, `Real.log_ne_zero_of_pos_of_ne_one`; and
  `Mathlib.Analysis.SpecialFunctions.Pow.Real`: `Real.log_rpow`.
- Mathlib `Mathlib.Analysis.SpecialFunctions.ExpDeriv`: `HasDerivAt.exp`.
- Mathlib `Mathlib.Analysis.SpecialFunctions.Log.Deriv`: `Real.abs_log_sub_add_sum_range_le`.
  `Mathlib.Analysis.SpecialFunctions.Complex.LogBounds` has the related complex bound
  `Complex.norm_log_one_add_sub_self_le`.
- Mathlib `Mathlib.Analysis.Complex.Exponential`: `Real.exp_bound`; its
  `Real.abs_exp_sub_one_sub_id_le` is the first-order exponential bound with constant `1`.
- Mathlib `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`: `Real.hasDerivAt_rpow_const`.
- Mathlib `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`: `integral_exp`, `integral_rpow`,
  `integral_one_div`, `integral_one_div_one_add_sq`; and
  `Mathlib.Analysis.SpecialFunctions.Integrability.Basic`:
  `intervalIntegral.intervalIntegrable_rpow'`.
- Mathlib `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`:
  `intervalIntegral.integral_comp_mul_left`, `intervalIntegral.integral_comp_add_left`; and
  `Mathlib.MeasureTheory.Integral.IntegralEqImproper`:
  `MeasureTheory.intervalIntegral_tendsto_integral`.
- Mathlib `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`: `integral_gaussian`,
  `integrable_exp_neg_mul_sq`, `integrable_exp_neg_mul_sq_iff`.
- T. M. Apostol, *Calculus*, Vol. 1, 2nd ed., Wiley, 1967 (logarithm, exponential, Taylor's
  formula).
-/

@[expose] public section

namespace ScalarCalculus

/-! ## A. Logarithms of positive dimensionless arguments

These supporting lemmas take the positivity of every logarithm argument as an explicit
hypothesis. They are private, so no parallel logarithm API is exported, and each is used below:
`log_mul_exp_of_pos` (product rule and the round trip `log (exp y) = y`) by
`hasDerivAt_log_expDecay`, and `log_mul_div_rpow_of_pos` (product, quotient and power rules) by
`hasDerivAt_logb_powerLaw`. Two further facts of this kind are used directly from Mathlib, which
already states them in the needed form: the round trip `Real.exp_log`, whose hypothesis is
`0 < x`, in `integral_expDecay_ratioTime`; and base conversion `Real.log_div_log`
(`Real.logb b x = Real.log x / Real.log b` holds by definition) in `hasDerivAt_logb_powerLaw`,
which applies it to a positive argument with an admissible base `0 < b`, `b ≠ 1`. -/

/-- Logarithm of a positive multiple `c * exp y` of an exponential, `0 < c` (for instance an
initial amount in units of a reference amount): the product rule and the round trip
`log (exp y) = y` give `log c + y`. -/
private lemma log_mul_exp_of_pos {c : ℝ} (hc : 0 < c) (y : ℝ) :
    Real.log (c * Real.exp y) = Real.log c + y := by
  rw [Real.log_mul hc.ne' (Real.exp_pos y).ne', Real.log_exp]

/-- Logarithm of a power-law value `c * (x / x₀) ^ r` for a positive prefactor `c` and positive
like quantities `x`, `x₀`: the product, power and quotient rules give
`log c + r * (log x - log x₀)`. -/
private lemma log_mul_div_rpow_of_pos {c x x₀ r : ℝ} (hc : 0 < c) (hx : 0 < x) (hx₀ : 0 < x₀) :
    Real.log (c * (x / x₀) ^ r) = Real.log c + r * (Real.log x - Real.log x₀) := by
  have hq : 0 < x / x₀ := div_pos hx hx₀
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hq r).ne', Real.log_rpow hq,
    Real.log_div hx.ne' hx₀.ne']

/-! ## B. Exponential decay -/

/-- **Derivative of exponential decay.** The profile `x ↦ exp (-k * x)` has derivative
`-k * exp (-k * x)` at every `x`. This holds for every real `k`; the decay reading is `0 < k`. -/
lemma hasDerivAt_expDecay (k x : ℝ) :
    HasDerivAt (fun x => Real.exp (-k * x)) (-k * Real.exp (-k * x)) x := by
  simpa [mul_comm] using ((hasDerivAt_id x).const_mul (-k)).exp

/-- **Exponential decay in semi-log coordinates.** For a positive initial value `0 < N₀`
(measured in units of a reference amount, so that `N₀ * exp (-k * t)` is a positive
dimensionless ratio), `t ↦ log (N₀ * exp (-k * t))` has derivative `-k` at every `t`: on a
semi-log plot the decay profile is a straight line of slope `-k`. This holds for every real
`k`; the decay reading is `0 < k`. -/
lemma hasDerivAt_log_expDecay {N₀ : ℝ} (hN₀ : 0 < N₀) (k t : ℝ) :
    HasDerivAt (fun t => Real.log (N₀ * Real.exp (-k * t))) (-k) t := by
  have h : (fun t => Real.log (N₀ * Real.exp (-k * t))) = fun t => -k * t + Real.log N₀ := by
    funext s
    rw [log_mul_exp_of_pos hN₀]
    ring
  rw [h]
  simpa using ((hasDerivAt_id t).const_mul (-k)).add_const (Real.log N₀)

/-- **Integral of exponential decay.** For a decay rate `0 < k` and every `t`, of either sign
(the interval integral is oriented), `∫ x in 0..t, exp (-k * x) = (1 - exp (-k * t)) / k`. -/
lemma integral_expDecay {k : ℝ} (hk : 0 < k) (t : ℝ) :
    ∫ x in (0)..t, Real.exp (-k * x) = (1 - Real.exp (-k * t)) / k := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (neg_ne_zero.mpr hk.ne'),
    integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

/-- **Exponential decay up to a ratio time.** For a decay rate `0 < k` and a positive
dimensionless target ratio `0 < q` (for instance `N(t) / N₀`), let `t_q = -log q / k`, so that
`exp (-k * t_q) = exp (log q) = q` (for `q = 1 / 2`, `t_q = log 2 / k` is the half-life). The
decay integral up to `t_q` is `(1 - q) / k`. -/
lemma integral_expDecay_ratioTime {k q : ℝ} (hk : 0 < k) (hq : 0 < q) :
    ∫ x in (0)..(-Real.log q / k), Real.exp (-k * x) = (1 - q) / k := by
  rw [integral_expDecay hk, show -k * (-Real.log q / k) = Real.log q by field_simp,
    Real.exp_log hq]

/-! ## C. Power laws -/

/-- **Power laws.** For every real exponent `r`, the power law `x ↦ x ^ r` (Mathlib's real
power `Real.rpow`) has derivative `r * x ^ (r - 1)` at each `0 < x`. If `-1 < r`, it is
interval integrable on `[0, 1]` and `∫ x in 0..1, x ^ r = 1 / (r + 1)`. The hypothesis
`-1 < r`, rather than `r ≠ -1`, is necessary: for `r < -1` the integrand is not integrable near
`0`, and the interval integral is Lean's junk value `0`. -/
lemma hasDerivAt_and_integral_powerLaw (r : ℝ) :
    (∀ x : ℝ, 0 < x → HasDerivAt (fun x => x ^ r) (r * x ^ (r - 1)) x) ∧
      (-1 < r → IntervalIntegrable (fun x : ℝ => x ^ r) MeasureTheory.volume 0 1 ∧
        ∫ x in (0)..1, x ^ r = 1 / (r + 1)) := by
  refine ⟨fun x hx => Real.hasDerivAt_rpow_const (Or.inl hx.ne'), fun hr => ?_⟩
  refine ⟨intervalIntegral.intervalIntegrable_rpow' hr, ?_⟩
  rw [integral_rpow (Or.inl hr), Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

/-- **Power laws in log-log coordinates.** For an admissible base `0 < b`, `b ≠ 1`, a positive
prefactor `c` and a positive reference scale `x₀`, write the input as `x = b ^ u`, so that
`u = logb b x`. Then `u ↦ logb b (c * (b ^ u / x₀) ^ r)` has derivative `r` at every `u`: on a
base-`b` log-log plot the power law is a straight line of slope `r`. -/
lemma hasDerivAt_logb_powerLaw {b c x₀ r : ℝ} (hb : 0 < b) (hb₁ : b ≠ 1) (hc : 0 < c)
    (hx₀ : 0 < x₀) (u : ℝ) :
    HasDerivAt (fun u => Real.logb b (c * (b ^ u / x₀) ^ r)) r u := by
  have hlog : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb hb₁
  have h : (fun u => Real.logb b (c * (b ^ u / x₀) ^ r)) =
      fun u => r * u + (Real.log c - r * Real.log x₀) / Real.log b := by
    funext v
    rw [← Real.log_div_log, log_mul_div_rpow_of_pos hc (Real.rpow_pos_of_pos hb v) hx₀,
      Real.log_rpow hb]
    field_simp
    ring
  rw [h]
  simpa using ((hasDerivAt_id u).const_mul r).add_const
    ((Real.log c - r * Real.log x₀) / Real.log b)

/-! ## D. Gaussians -/

/-- **Gaussian integral.** For `0 < a`, the Gaussian `x ↦ exp (-a * x ^ 2)` is integrable on
`ℝ`, its integral over `ℝ` is `√(π / a)`, and this is also its improper integral:
`∫ x in α..β, exp (-a * x ^ 2) → √(π / a)` as `α → -∞` and `β → ∞` independently.
Integrability is what makes the value meaningful: for `a ≤ 0` the Gaussian is not integrable
(`integrable_exp_neg_mul_sq_iff`), and Mathlib's `integral_gaussian` still reads
`∫ = √(π / a)`, but both sides are the junk value `0`. -/
lemma integrable_and_integral_gaussian {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun x : ℝ => Real.exp (-a * x ^ 2)) ∧
      ∫ x : ℝ, Real.exp (-a * x ^ 2) = Real.sqrt (Real.pi / a) ∧
      Filter.Tendsto (fun p : ℝ × ℝ => ∫ x in p.1..p.2, Real.exp (-a * x ^ 2))
        (Filter.atBot ×ˢ Filter.atTop) (nhds (Real.sqrt (Real.pi / a))) := by
  have hint := integrable_exp_neg_mul_sq ha
  refine ⟨hint, integral_gaussian a, ?_⟩
  rw [← integral_gaussian a]
  exact MeasureTheory.intervalIntegral_tendsto_integral hint Filter.tendsto_fst
    Filter.tendsto_snd

/-- **Derivative of the Gaussian.** The Gaussian `x ↦ exp (-a * x ^ 2)` has derivative
`-2 * a * x * exp (-a * x ^ 2)` at every `x`. This holds for every real `a`; the Gaussian reading
is `0 < a`. -/
lemma hasDerivAt_gaussian (a x : ℝ) :
    HasDerivAt (fun x => Real.exp (-a * x ^ 2)) (-2 * a * x * Real.exp (-a * x ^ 2)) x := by
  convert ((hasDerivAt_pow 2 x).const_mul (-a)).exp using 1
  push_cast
  ring

/-! ## E. Rational rates -/

/-- **Rational rates.** Over `[0, t]`, the Lorentzian rate `1 / (1 + x ^ 2)` integrates to
`arctan t` for every real `t`, and the hyperbolic rate `1 / (1 + x)` integrates to
`log (1 + t)` whenever the logarithm argument `1 + t` is positive (in particular for `0 ≤ t`). -/
lemma integral_rationalRates (t : ℝ) :
    ∫ x in (0)..t, 1 / (1 + x ^ 2) = Real.arctan t ∧
      (0 < 1 + t → ∫ x in (0)..t, 1 / (1 + x) = Real.log (1 + t)) := by
  refine ⟨by rw [integral_one_div_one_add_sq, Real.arctan_zero, sub_zero], fun ht => ?_⟩
  have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + t) := by
    rw [Set.mem_uIcc]
    rintro (h | h) <;> linarith [h.1, h.2]
  rw [intervalIntegral.integral_comp_add_left (fun x => 1 / x) 1, add_zero, integral_one_div h0,
    div_one]

/-! ## F. Taylor remainder bounds on compact intervals -/

/-- The logarithmic series of `log (1 + x)` to fourth order, with remainder at most
`2 * |x| ^ 5` on `|x| ≤ 1 / 2`. -/
private lemma abs_log_one_add_sub_quartic_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)| ≤ 2 * |x| ^ 5 := by
  have h1 : |-x| < 1 := by rw [abs_neg]; linarith
  have hd : 0 < 1 - |x| := by linarith
  calc |Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)|
      = |∑ i ∈ Finset.range 4, (-x) ^ (i + 1) / (i + 1) + Real.log (1 - -x)| := by
        congr 1
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add]
        push_cast
        ring
    _ ≤ |-x| ^ (4 + 1) / (1 - |-x|) := Real.abs_log_sub_add_sum_range_le h1 4
    _ = |x| ^ 5 / (1 - |x|) := by rw [abs_neg]
    _ ≤ 2 * |x| ^ 5 := by
      rw [div_le_iff₀ hd]
      nlinarith [mul_nonneg (pow_nonneg (abs_nonneg x) 5) (by linarith : (0 : ℝ) ≤ 1 / 2 - |x|)]

/-- **First-order bound for `log (1 + x)`.** On the compact interval `|x| ≤ 1 / 2`, where the
logarithm argument `1 + x ∈ [1 / 2, 3 / 2]` is positive (the ratio of a perturbed to a reference
quantity, with relative change `x`), `|log (1 + x) - x| ≤ x ^ 2`. This is an inequality on that
interval only, not an equality, and nothing is asserted outside the interval. -/
lemma abs_log_one_add_sub_linear_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have hR := abs_log_one_add_sub_quartic_le hx
  have ha : 0 ≤ |x| := abs_nonneg x
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have h2 : |x ^ 2 / 2| = |x| ^ 2 / 2 := by rw [abs_div, abs_pow]; norm_num
  have h3 : |x ^ 3 / 3| = |x| ^ 3 / 3 := by rw [abs_div, abs_pow]; norm_num
  have h4 : |x ^ 4 / 4| = |x| ^ 4 / 4 := by rw [abs_div, abs_pow]; norm_num
  have e : Real.log (1 + x) - x =
      (Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)) - x ^ 2 / 2 + x ^ 3 / 3 -
        x ^ 4 / 4 := by ring
  rw [e]
  calc _ ≤ |Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)| + |x ^ 2 / 2| +
        |x ^ 3 / 3| + |x ^ 4 / 4| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ x ^ 2 := by
      rw [h2, h3, h4]
      have hp3 : |x| ^ 3 ≤ |x| ^ 2 / 2 := by nlinarith [pow_nonneg ha 2]
      have hp4 : |x| ^ 4 ≤ |x| ^ 2 / 4 := by nlinarith [pow_nonneg ha 2, pow_nonneg ha 3]
      have hp5 : |x| ^ 5 ≤ |x| ^ 2 / 8 := by
        nlinarith [pow_nonneg ha 2, pow_nonneg ha 3, pow_nonneg ha 4]
      linarith [pow_nonneg ha 2]

/-- **Second-order bound for `log (1 + x)`.** On the compact interval `|x| ≤ 1 / 2`, where the
logarithm argument `1 + x ∈ [1 / 2, 3 / 2]` is positive,
`|log (1 + x) - (x - x ^ 2 / 2)| ≤ |x| ^ 3`. This is an inequality on that interval only, not an
equality, and nothing is asserted outside the interval. -/
lemma abs_log_one_add_sub_quadratic_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ |x| ^ 3 := by
  have hR := abs_log_one_add_sub_quartic_le hx
  have ha : 0 ≤ |x| := abs_nonneg x
  have h3 : |x ^ 3 / 3| = |x| ^ 3 / 3 := by rw [abs_div, abs_pow]; norm_num
  have h4 : |x ^ 4 / 4| = |x| ^ 4 / 4 := by rw [abs_div, abs_pow]; norm_num
  have e : Real.log (1 + x) - (x - x ^ 2 / 2) =
      (Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)) + x ^ 3 / 3 - x ^ 4 / 4 := by
    ring
  rw [e]
  calc _ ≤ |Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4)| + |x ^ 3 / 3| +
        |x ^ 4 / 4| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ |x| ^ 3 := by
      rw [h3, h4]
      have hp4 : |x| ^ 4 ≤ |x| ^ 3 / 2 := by nlinarith [pow_nonneg ha 3]
      have hp5 : |x| ^ 5 ≤ |x| ^ 3 / 4 := by nlinarith [pow_nonneg ha 3, pow_nonneg ha 4]
      linarith [pow_nonneg ha 3]

/-- **First-order bound for `exp x`.** On the compact interval `|x| ≤ 1`,
`|exp x - (1 + x)| ≤ 3 / 4 * x ^ 2`. The constant `3 / 4` comes from Mathlib's `Real.exp_bound`
and is sharper than `1`. This is an inequality on that interval only, not an equality, and
nothing is asserted outside the interval. -/
lemma abs_exp_sub_linear_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x)| ≤ 3 / 4 * x ^ 2 := by
  have h := Real.exp_bound hx (n := 2) (by norm_num)
  have hs : ∑ m ∈ Finset.range 2, x ^ m / (m.factorial : ℝ) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [hs] at h
  calc _ ≤ _ := h
    _ = 3 / 4 * x ^ 2 := by
      rw [sq_abs]
      norm_num [Nat.factorial]
      ring

/-- **Second-order bound for `exp x`.** On the compact interval `|x| ≤ 1`,
`|exp x - (1 + x + x ^ 2 / 2)| ≤ 2 / 9 * |x| ^ 3`. The constant `2 / 9` comes from Mathlib's
`Real.exp_bound` and is sharper than `1`. This is an inequality on that interval only, not an
equality, and nothing is asserted outside the interval. -/
lemma abs_exp_sub_quadratic_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ 2 / 9 * |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at h
  calc _ ≤ _ := h
    _ = 2 / 9 * |x| ^ 3 := by
      norm_num [Nat.factorial]
      ring

end ScalarCalculus
