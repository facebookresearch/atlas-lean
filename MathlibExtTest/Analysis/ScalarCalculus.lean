/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ScalarCalculus

/-!
# Tests for `MathlibExt.Analysis.ScalarCalculus`

Exact values, Lean's totalisation boundaries, countermodels outside the stated intervals and
domains, and worked examples that combine several public results.
-/

@[expose] public section

open ScalarCalculus

namespace MathlibExtTest.ScalarCalculus

/-! ## Exact values -/

/-- `log` inverts `exp`. -/
example : Real.log (Real.exp 2) = 2 := Real.log_exp 2

/-- `exp` inverts `log` on the positive argument `3`. -/
example : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)

/-- Base conversion at an exact case: `logb 2 8 = 3`. -/
example : Real.logb 2 8 = 3 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- The decay integral vanishes on the empty interval (`k = 1`, `t = 0`). -/
example : ∫ x in (0)..0, Real.exp (-1 * x) = 0 := by
  rw [integral_expDecay one_pos 0]
  simp

/-- The decay integral at `k = 1` up to `t = log 2` is `1 / 2`. -/
example : ∫ x in (0)..Real.log 2, Real.exp (-1 * x) = 1 / 2 := by
  rw [integral_expDecay one_pos (Real.log 2), neg_one_mul, Real.exp_neg,
    Real.exp_log (by norm_num)]
  norm_num

/-- Decay up to the half-life `log 2 / k` (the ratio time for `q = 1 / 2`) accumulates
`1 / (2 * k)`. -/
example {k : ℝ} (hk : 0 < k) :
    ∫ x in (0)..(Real.log 2 / k), Real.exp (-k * x) = 1 / (2 * k) := by
  have h := integral_expDecay_ratioTime hk (by norm_num : (0 : ℝ) < 1 / 2)
  rw [one_div 2, Real.log_inv, neg_neg] at h
  rw [h]
  field_simp
  norm_num

/-- On a semi-log plot, `5 * exp (-2 * t)` has slope `-2`. -/
example : HasDerivAt (fun t => Real.log (5 * Real.exp (-2 * t))) (-2) 1 :=
  hasDerivAt_log_expDecay (by norm_num) 2 1

/-- The Gaussian `exp (-x ^ 2)` is integrable on `ℝ`. -/
example : MeasureTheory.Integrable (fun x : ℝ => Real.exp (-1 * x ^ 2)) :=
  (integrable_and_integral_gaussian one_pos).1

/-- The Gaussian integral at `a = 1` is `√π`. -/
example : ∫ x : ℝ, Real.exp (-1 * x ^ 2) = Real.sqrt Real.pi := by
  rw [(integrable_and_integral_gaussian one_pos).2.1, div_one]

/-- The improper Gaussian limit specialises to symmetric truncations `∫ x in -R..R`. -/
example : Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, Real.exp (-1 * x ^ 2)) Filter.atTop
    (nhds (Real.sqrt Real.pi)) := by
  have h := (integrable_and_integral_gaussian one_pos).2.2
  rw [div_one] at h
  exact h.comp (Filter.tendsto_neg_atTop_atBot.prodMk Filter.tendsto_id)

/-- The Gaussian has a critical point at `0`. -/
example (a : ℝ) : HasDerivAt (fun x => Real.exp (-a * x ^ 2)) 0 0 := by
  simpa using hasDerivAt_gaussian a 0

/-- The Lorentzian rate integrates to `π / 4` over `[0, 1]`. -/
example : ∫ x in (0)..1, 1 / (1 + x ^ 2) = Real.pi / 4 := by
  rw [(integral_rationalRates 1).1, Real.arctan_one]

/-- The power law `x ^ 2` integrates to `1 / 3` over `[0, 1]`. -/
example : ∫ x in (0)..1, x ^ (2 : ℝ) = 1 / 3 := by
  rw [((hasDerivAt_and_integral_powerLaw 2).2 (by norm_num)).2]
  norm_num

/-- The singular power law `x ^ (-1 / 2)` is integrable on `[0, 1]`, with integral `2`. -/
example : IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) MeasureTheory.volume 0 1 ∧
    ∫ x in (0)..1, x ^ (-1 / 2 : ℝ) = 2 := by
  obtain ⟨hi, hv⟩ := (hasDerivAt_and_integral_powerLaw (-1 / 2)).2 (by norm_num)
  exact ⟨hi, by rw [hv]; norm_num⟩

/-- At `x = 1` the power law `x ^ r` has slope `r`. -/
example (r : ℝ) : HasDerivAt (fun x => x ^ r) r 1 := by
  simpa using (hasDerivAt_and_integral_powerLaw r).1 1 one_pos

/-- On a base-`10` log-log plot, `3 * (x / 1) ^ 2` has slope `2`. -/
example : HasDerivAt (fun u : ℝ => Real.logb 10 (3 * ((10 : ℝ) ^ u / 1) ^ (2 : ℝ))) 2 0 :=
  hasDerivAt_logb_powerLaw (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0

/-- First-order logarithm bound at `x = 1 / 2`: `|log (3 / 2) - 1 / 2| ≤ 1 / 4`. -/
example : |Real.log (3 / 2) - 1 / 2| ≤ 1 / 4 := by
  have h := abs_log_one_add_sub_linear_le (x := 1 / 2) (by norm_num [abs_of_pos])
  norm_num at h
  exact h

/-- Second-order logarithm bound at `x = 1 / 2`: `|log (3 / 2) - 3 / 8| ≤ 1 / 8`. -/
example : |Real.log (3 / 2) - 3 / 8| ≤ 1 / 8 := by
  have h := abs_log_one_add_sub_quadratic_le (x := 1 / 2) (by norm_num [abs_of_pos])
  norm_num at h
  exact h

/-- At the other endpoint `x = -1 / 2`, the second-order logarithm bound gives
`1 / 2 ≤ log 2 ≤ 3 / 4`. -/
example : 1 / 2 ≤ Real.log 2 ∧ Real.log 2 ≤ 3 / 4 := by
  have h := abs_log_one_add_sub_quadratic_le (x := -1 / 2) (by norm_num [abs_div])
  rw [show (1 : ℝ) + -1 / 2 = 2⁻¹ by norm_num, Real.log_inv] at h
  have h' := abs_le.mp h
  norm_num at h'
  constructor <;> linarith [h'.1, h'.2]

/-- First-order exponential bound at `x = 1`: `|e - 2| ≤ 3 / 4`. -/
example : |Real.exp 1 - 2| ≤ 3 / 4 := by
  have h := abs_exp_sub_linear_le (x := 1) (by norm_num)
  norm_num at h
  exact h

/-- Second-order exponential bound at `x = 1`: `|e - 5 / 2| ≤ 2 / 9`. -/
example : |Real.exp 1 - 5 / 2| ≤ 2 / 9 := by
  have h := abs_exp_sub_quadratic_le (x := 1) (by norm_num)
  norm_num at h
  exact h

/-! ## Boundaries of Lean's total functions

`Real.log` is total, so the identities below are conventions, not physics. The physical domain
of a logarithm excludes `0` and negative arguments, and every logarithm statement of the module
requires a positive argument. -/

/-- Lean's convention `Real.log 0 = 0`; `0` is outside the physical domain. -/
example : Real.log 0 = 0 := Real.log_zero

/-- Without `0 < x` the round trip `exp (log x) = x` fails: at `x = 0` and at `x = -2`. -/
example : Real.exp (Real.log 0) = 1 ∧ Real.exp (Real.log (-2)) = 2 ∧
    ¬ ∀ x : ℝ, Real.exp (Real.log x) = x := by
  have h0 : Real.exp (Real.log 0) = 1 := by rw [Real.log_zero, Real.exp_zero]
  refine ⟨h0, ?_, fun h => by simpa [h0] using h 0⟩
  rw [Real.log_neg_eq_log, Real.exp_log (by norm_num)]

/-- Without `0 < a`, Mathlib's Gaussian identity only equates junk values: at `a = -1` the
integrand is not integrable and the right-hand side `√(π / a)` is `0`. -/
example : ¬ MeasureTheory.Integrable (fun x : ℝ => Real.exp (-(-1) * x ^ 2)) ∧
    ∫ x : ℝ, Real.exp (-(-1) * x ^ 2) = 0 := by
  refine ⟨fun h => absurd (integrable_exp_neg_mul_sq_iff.mp h) (by norm_num), ?_⟩
  rw [integral_gaussian, Real.sqrt_eq_zero', div_neg, div_one, neg_nonpos]
  exact Real.pi_pos.le

/-- The power-law integral needs `-1 < r`, not merely `r ≠ -1`: at `r = -2` the integrand is not
integrable on `[0, 1]`, the interval integral is the junk value `0`, and `1 / (r + 1) = -1`. -/
example : ∫ x in (0)..1, x ^ (-2 : ℝ) = 0 ∧ 1 / ((-2 : ℝ) + 1) = -1 := by
  refine ⟨intervalIntegral.integral_undef fun h => ?_, by norm_num⟩
  have hIoo := ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h).mono_set
    Set.Ioo_subset_Ioc_self
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mp hIoo
  norm_num at this

/-! ## Countermodels outside the stated intervals -/

/-- Both logarithm bounds fail at a point outside `|x| ≤ 1 / 2`: at `x = exp (-3) - 1`, where
`log (1 + x) = -3` and `|x| > 1 / 2`, the first-order error `2 + exp (-3)` exceeds `x ^ 2`, and
the second-order error exceeds `|x| ^ 3`. -/
example : 1 / 2 < |Real.exp (-3) - 1| ∧
    (Real.exp (-3) - 1) ^ 2 < |Real.log (1 + (Real.exp (-3) - 1)) - (Real.exp (-3) - 1)| ∧
    |Real.exp (-3) - 1| ^ 3 < |Real.log (1 + (Real.exp (-3) - 1)) -
      ((Real.exp (-3) - 1) - (Real.exp (-3) - 1) ^ 2 / 2)| := by
  set y := Real.exp (-3) with hy_def
  have hy : 0 < y := Real.exp_pos (-3)
  have h4 : (3 : ℝ) + 1 ≤ Real.exp 3 := Real.add_one_le_exp 3
  have hprod : y * Real.exp 3 = 1 := by rw [hy_def, ← Real.exp_add]; norm_num
  have hlt : y < 1 / 2 := by nlinarith
  have hlog : Real.log (1 + (y - 1)) = -3 := by rw [add_sub_cancel, hy_def, Real.log_exp]
  have habs : |y - 1| = 1 - y := by rw [abs_of_neg (by linarith)]; ring
  have e1 : |Real.log (1 + (y - 1)) - (y - 1)| = 2 + y := by
    rw [hlog, abs_of_neg (by linarith)]; ring
  have e2 : |Real.log (1 + (y - 1)) - ((y - 1) - (y - 1) ^ 2 / 2)| =
      3 / 2 + 2 * y - y ^ 2 / 2 := by
    rw [hlog, abs_of_neg (by nlinarith)]; ring
  rw [habs, e1, e2]
  refine ⟨by linarith, by nlinarith, ?_⟩
  nlinarith [mul_pos hy (by linarith : (0 : ℝ) < 5 - 7 / 2 * y), pow_pos hy 3]

/-- The first-order exponential bound fails at a point outside `|x| ≤ 1`: at `x = 2` the error
`exp 2 - 3` exceeds `3 / 4 * 2 ^ 2 = 3`, since `exp 2 ≥ (5 / 2) ^ 2`. -/
example : 3 / 4 * (2 : ℝ) ^ 2 < |Real.exp 2 - (1 + 2)| := by
  have h1 : 1 + 1 + (1 : ℝ) ^ 2 / 2 ≤ Real.exp 1 := Real.quadratic_le_exp_of_nonneg zero_le_one
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [abs_of_pos (by nlinarith)]
  nlinarith

/-- The second-order exponential bound fails at a point outside `|x| ≤ 1`: at `x = 3` the error
`exp 3 - 17 / 2` exceeds `2 / 9 * 3 ^ 3 = 6`, since `exp 3 ≥ (5 / 2) ^ 3`. -/
example : 2 / 9 * |(3 : ℝ)| ^ 3 < |Real.exp 3 - (1 + 3 + 3 ^ 2 / 2)| := by
  have h1 : 1 + 1 + (1 : ℝ) ^ 2 / 2 ≤ Real.exp 1 := Real.quadratic_le_exp_of_nonneg zero_le_one
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have he : (5 / 2 : ℝ) ^ 3 ≤ Real.exp 3 := by
    rw [h3]
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 3
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by nlinarith)]
  nlinarith

/-! ## Worked examples combining public results -/

/-- Decay integral and first-order exponential bound: for `0 < k` and `|k * t| ≤ 1`, the
accumulated decay `∫ x in 0..t, exp (-k * x)` is within `3 / 4 * k * t ^ 2` of `t`. -/
example {k t : ℝ} (hk : 0 < k) (hkt : |k * t| ≤ 1) :
    |(∫ x in (0)..t, Real.exp (-k * x)) - t| ≤ 3 / 4 * k * t ^ 2 := by
  have hb := abs_exp_sub_linear_le (x := -k * t) (by rwa [neg_mul, abs_neg])
  rw [integral_expDecay hk t]
  have e : (1 - Real.exp (-k * t)) / k - t = -(Real.exp (-k * t) - (1 + -k * t)) / k := by
    field_simp
    ring
  rw [e, abs_div, abs_neg, abs_of_pos hk, div_le_iff₀ hk]
  calc _ ≤ 3 / 4 * (-k * t) ^ 2 := hb
    _ = 3 / 4 * k * t ^ 2 * k := by ring

/-- Hyperbolic-rate integral and first-order logarithm bound: for `|t| ≤ 1 / 2`,
`|∫ x in 0..t, 1 / (1 + x) - t| ≤ t ^ 2`. -/
example {t : ℝ} (ht : |t| ≤ 1 / 2) : |(∫ x in (0)..t, 1 / (1 + x)) - t| ≤ t ^ 2 := by
  have h1 : 0 < 1 + t := by linarith [neg_abs_le t]
  rw [(integral_rationalRates t).2 h1]
  exact abs_log_one_add_sub_linear_le ht

/-- Differentiating the decay integral identity recovers the integrand (fundamental theorem of
calculus), combining `integral_expDecay` and `hasDerivAt_expDecay`. -/
example {k t : ℝ} (hk : 0 < k) :
    HasDerivAt (fun t => ∫ x in (0)..t, Real.exp (-k * x)) (Real.exp (-k * t)) t := by
  rw [show (fun t => ∫ x in (0)..t, Real.exp (-k * x)) = fun t => (1 - Real.exp (-k * t)) / k
    from funext (integral_expDecay hk)]
  convert ((hasDerivAt_expDecay k t).const_sub 1).div_const k using 1
  field_simp

/-- First-order logarithm bound converted to base `2`: for `|x| ≤ 1 / 2`,
`|logb 2 (1 + x) - x / log 2| ≤ x ^ 2 / log 2`. -/
example {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.logb 2 (1 + x) - x / Real.log 2| ≤ x ^ 2 / Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Real.log_div_log, ← sub_div, abs_div, abs_of_pos hl]
  exact div_le_div_of_nonneg_right (abs_log_one_add_sub_linear_le hx) hl.le

end MathlibExtTest.ScalarCalculus

/-! ## Axiom audit of every public declaration -/

#print axioms ScalarCalculus.hasDerivAt_expDecay
#print axioms ScalarCalculus.hasDerivAt_log_expDecay
#print axioms ScalarCalculus.integral_expDecay
#print axioms ScalarCalculus.integral_expDecay_ratioTime
#print axioms ScalarCalculus.hasDerivAt_and_integral_powerLaw
#print axioms ScalarCalculus.hasDerivAt_logb_powerLaw
#print axioms ScalarCalculus.integrable_and_integral_gaussian
#print axioms ScalarCalculus.hasDerivAt_gaussian
#print axioms ScalarCalculus.integral_rationalRates
#print axioms ScalarCalculus.abs_log_one_add_sub_linear_le
#print axioms ScalarCalculus.abs_log_one_add_sub_quadratic_le
#print axioms ScalarCalculus.abs_exp_sub_linear_le
#print axioms ScalarCalculus.abs_exp_sub_quadratic_le
