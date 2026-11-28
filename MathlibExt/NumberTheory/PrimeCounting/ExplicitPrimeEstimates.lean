/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import MathlibExt.NumberTheory.PrimeCounting.ChebyshevThetaBounds

/-!
# Explicit Chebyshev estimates and bounded prime counting

Chebyshev's theta function has explicit upper and lower estimates for real `x > 1`,
with simpler linear estimates when `x ≥ 65536`. A computable primality indicator
agrees with the usual indicator for `p < 363 ^ 2`; summing it counts primes up to a
natural number in the same range.

## References

* Sadegh Nazardonyavi and Semyon Yakubovich, *Extremely Abundant Numbers and the Riemann
  Hypothesis*, Journal of Integer Sequences 17 (2014), Article 14.2.8, Lemma 8.
* P. L. Chebyshev, *Mémoire sur les nombres premiers*, Journal de Mathématiques Pures et
  Appliquées 17 (1852), 366–390, p. 379, the source of the theta estimates in Lemma 8.
* The numerical estimates and bounded primality indicator were originally formalized in
  `MathlibExt.NumberTheory.PrimeCounting.LaishramRamanujanPrimeBound`.
-/

namespace MetaMathlibExt.ExplicitPrimeEstimates

open Real Chebyshev

private noncomputable def chebyshevConstant : ℝ :=
  log (((2 : ℝ) ^ (1 / 2 : ℝ) * 3 ^ (1 / 3 : ℝ) * 5 ^ (1 / 5 : ℝ)) / 30 ^ (1 / 30 : ℝ))

private lemma constant_bounds : 0.921 < chebyshevConstant ∧ chebyshevConstant < 0.922 := by
  unfold chebyshevConstant
  rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity)]
  simp only [log_rpow (by norm_num : (0 : ℝ) < 2), log_rpow (by norm_num : (0 : ℝ) < 3),
    log_rpow (by norm_num : (0 : ℝ) < 5), log_rpow (by norm_num : (0 : ℝ) < 30)]
  rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, log_mul (by norm_num) (by norm_num),
    log_mul (by norm_num) (by norm_num)]
  constructor <;> linarith [log_two_gt_d9, log_two_lt_d9, log_three_gt_d9, log_three_lt_d9,
    log_five_gt_d9, log_five_lt_d9]

/-- For real `x > 1`, Chebyshev's theta function is at most
`1.107 * x + (log x)^2 + 3 * log x + 2` and at least
`0.921 * x - 2.22 * √x - (log x)^2 / 2 - 4 * log x - 3`. -/
public lemma theta_bounds (x : ℝ) (hx : 1 < x) :
    theta x ≤ 1.107 * x + (log x)^2 + 3 * log x + 2 ∧
    0.921 * x - 2.22 * √x - (log x)^2 / 2 - 4 * log x - 3 ≤ theta x := by
  obtain ⟨hu, hl⟩ := chebyshev_theta_explicit_bounds x hx
  change _ * chebyshevConstant * x - chebyshevConstant * √x + _ + _ + _ > theta x at hu
  change theta x > chebyshevConstant * x - _ * chebyshevConstant * √x - _ - _ - _ at hl
  have hlog : 0 ≤ log x := log_nonneg hx.le
  have h6 : 1.7 < log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
    linarith [log_two_gt_d9, log_three_gt_d9]
  have hu' : 5 / (4 * log 6) ≤ (1 : ℝ) := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hl' : 5 / (8 * log 6) ≤ (1 : ℝ) / 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have ⟨hA, hA'⟩ := constant_bounds
  have hx0 : 0 ≤ x := by linarith
  constructor
  · nlinarith only [hu, mul_le_mul_of_nonneg_right hA'.le hx0,
      mul_nonneg (show 0 ≤ chebyshevConstant by linarith) (sqrt_nonneg x),
      mul_le_mul_of_nonneg_right hu' (sq_nonneg (log x)), hlog, hx0]
  · nlinarith only [hl, mul_le_mul_of_nonneg_right hA.le hx0,
      mul_le_mul_of_nonneg_right hA'.le (sqrt_nonneg x),
      mul_le_mul_of_nonneg_right hl' (sq_nonneg (log x)), hlog, sqrt_nonneg x]

private lemma log_65536 : log 65536 = 16 * log 2 := by
  rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, log_pow]
  norm_num

/-- For every real `x ≥ 65536`, Chebyshev's theta function lies between `0.91 * x`
and `1.11 * x`. -/
public lemma theta_bounds_of_65536_le (x : ℝ) (hx : 65536 ≤ x) :
    theta x ≤ 1.11 * x ∧ 0.91 * x ≤ theta x := by
  have hexp : exp 2 ≤ (65536 : ℝ) := by
    rw [← le_log_iff_exp_le (by norm_num), log_65536]
    linarith [log_two_gt_d9]
  have h := log_div_sqrt_antitoneOn hexp (hexp.trans hx) hx
  have hs : 256 ≤ √x := by
    exact (le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hs' := sq_sqrt (show 0 ≤ x by linarith)
  have hlog : log x ≤ 0.044 * √x := by
    change log x / √x ≤ log 65536 / √65536 at h
    rw [log_65536, show √(65536 : ℝ) = 256 by rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num] at h
    apply (div_le_iff₀ (show 0 < √x by linarith)).1
    exact h.trans (by linarith [log_two_lt_d9])
  have hlog0 := log_nonneg (show 1 ≤ x by linarith)
  have hlog2 := mul_self_le_mul_self hlog0 hlog
  have hsx : 256 * √x ≤ x := by nlinarith [mul_nonneg (sqrt_nonneg x) (sub_nonneg.mpr hs)]
  obtain ⟨hu, hl⟩ := theta_bounds x (by linarith)
  constructor <;> nlinarith only [hlog, hlog2, hs', hsx, hu, hl, hx]

/-- The sum of `log p` over primes `p ≤ 4096` is at least 3400. -/
public lemma le_theta_4096 : 3400 ≤ theta 4096 := by
  have h := (theta_bounds 4096 (by norm_num)).2
  rw [show √(4096 : ℝ) = 64 by rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num,
    show (4096 : ℝ) = 2 ^ 12 by norm_num, log_pow] at h
  norm_num at h
  nlinarith [log_two_lt_d9, log_two_gt_d9,
    mul_self_le_mul_self (log_nonneg (by norm_num : 1 ≤ (2 : ℝ))) log_two_lt_d9.le]

/-- A computable primality indicator for natural numbers `p < 363 ^ 2`. It checks
primality directly for `p ≤ 362` and uses coprimality with `362!` above that. -/
@[expose] public def primeFlag (p : ℕ) : ℕ :=
  if p ≤ 362 then (if p.Prime then 1 else 0)
  else if p.gcd (Nat.factorial 362) = 1 then 1 else 0

/-- Below `363 ^ 2`, `primeFlag` is one on primes and zero on all other natural numbers. -/
public lemma primeFlag_eq {p : ℕ} (hp : p < 363 ^ 2) :
    primeFlag p = if p.Prime then 1 else 0 := by
  by_cases hs : p ≤ 362
  · simp [primeFlag, hs]
  have hiff : p.gcd (Nat.factorial 362) = 1 ↔ p.Prime := by
    rw [← Nat.coprime_iff_gcd_eq_one]
    refine ⟨fun hc => ?_, fun h => h.coprime_factorial_of_lt (by omega)⟩
    by_contra h
    have hfac := Nat.minFac_sq_le_self (by omega : 0 < p) h
    have hg := (Nat.coprime_factorial_iff (by omega : p ≠ 1)).mp hc
    nlinarith only [hp, hfac, Nat.mul_self_le_mul_self (show 363 ≤ p.minFac by omega)]
  simp only [primeFlag, ite_eq_right hs, hiff]

/-- For `n < 363 ^ 2`, counting the entries flagged by `primeFlag` from zero through
`n` computes the number of primes at most `n`. -/
public lemma primeCounting_eq_countP_primeFlag {n : ℕ} (hn : n < 363 ^ 2) :
    Nat.primeCounting n = (List.range (n + 1)).countP (fun p ↦ primeFlag p == 1) := by
  change (List.range (n + 1)).countP (fun p ↦ decide p.Prime) = _
  apply List.countP_congr
  intro p hp
  rw [primeFlag_eq (by have := List.mem_range.mp hp; omega)]
  by_cases h : p.Prime <;> simp [h]

/-- There are 564 primes at most 4096. -/
public lemma primeCounting_4096 : Nat.primeCounting 4096 = 564 := by
  rw [primeCounting_eq_countP_primeFlag (by decide)]
  decide +kernel

end MetaMathlibExt.ExplicitPrimeEstimates
