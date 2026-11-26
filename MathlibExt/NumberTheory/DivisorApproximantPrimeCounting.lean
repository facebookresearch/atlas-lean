/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# Exponential approximation of the divisor count and divisor sum

The exponential weights equal one on the divisors and are at most $e^{-nk}$ on the
nondivisors. The total contribution of the nondivisors is therefore bounded by a
geometric sum with ratio $e^{-n}$.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

/-- **Exponential approximation of the divisibility indicator.** Let $A$ be a real-valued
function of two natural numbers such that $A(k, n) \sin^2(n\pi/k) \ge 1$ for all natural numbers
$k, n$ with $1 \le k \le n$ and $k \nmid n$. Then for all natural numbers $k, n$ with
$1 \le k \le n$,
$$\left| e^{-nkA(k, n)\sin^2(n\pi/k)} - \delta_{k \mid n} \right| \le e^{-nk},$$
where $\delta_{k \mid n}$ is $1$ if $k$ divides $n$ and $0$ otherwise.

When $k \mid n$ the difference is $0$; otherwise it lies in $(0, e^{-nk}]$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 1 (`integers-2026-A46-lem-1`). -/
public theorem abs_exp_approx_sub_dvd_indicator_le (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2)
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    |Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) - (if k ∣ n then 1 else 0)| ≤
      Real.exp (-(n * k : ℝ)) := by
  split_ifs with hd
  · -- At a divisor the sine vanishes, so the weight is exactly one.
    obtain ⟨d, hd'⟩ := hd
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have harg : (n : ℝ) * Real.pi / k = d * Real.pi := by
      rw [hd', Nat.cast_mul]
      field_simp
    simpa [harg, Real.sin_nat_mul_pi] using (Real.exp_pos (-(n * k : ℝ))).le
  · -- At a nondivisor the hypothesis bounds the exponent by `-n k`.
    rw [sub_zero, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hA k n hk hkn hd)
      (show 0 ≤ (n : ℝ) * k by positivity)
    linarith only [h]

private theorem sum_abs_exp_sub_indicator_lt (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, |Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) -
      (if k ∣ n then 1 else 0)| < 1 / (Real.exp n - 1) := by
  let w (k : ℕ) := Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from hn)
  have hterm (k : ℕ) (hk : k ∈ Icc 1 n) :
      |w k - (if k ∣ n then 1 else 0)| ≤ Real.exp (-n) ^ k := by
    obtain ⟨hk₁, hkn⟩ := mem_Icc.mp hk
    rw [← Real.exp_nat_mul, show (k : ℝ) * -n = -(n * k) by ring]
    exact abs_exp_approx_sub_dvd_indicator_le A hA k n hk₁ hkn
  have hlt : Real.exp (-n) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hn')
  calc
    _ ≤ ∑ k ∈ Icc 1 n, Real.exp (-n) ^ k := sum_le_sum hterm
    _ < Real.exp (-n) / (1 - Real.exp (-n)) := by
      rw [← Ico_add_one_right_eq_Icc, geom_sum_Ico' hlt.ne (by omega), pow_one]
      exact (div_lt_div_iff_of_pos_right (sub_pos.mpr hlt)).mpr (sub_lt_self _ (by positivity))
    _ = 1 / (Real.exp n - 1) := by
      rw [Real.exp_neg]
      field_simp

/-- **Exponential approximation of the divisor-counting function.** Let $A$ be a real-valued
function of two natural numbers such that $A(k, n) \sin^2(n\pi/k) \ge 1$ for all natural numbers
$k, n$ with $1 \le k \le n$ and $k \nmid n$. For a natural number $n$ let $\tau(n)$ be the number
of positive divisors of $n$ and
$$\tilde\tau(n) = \sum_{k=1}^{n} e^{-nkA(k, n)\sin^2(n\pi/k)}.$$
Then $\tilde\tau(n) - \tau(n) = O\left(\frac{1}{e^n - 1}\right)$ as $n \to \infty$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Lemma 2 (`integers-2026-A46-lem-2`). -/
public theorem divisorCountApprox_sub_isBigO (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2) :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) -
        (n.divisors.card : ℝ)) =O[atTop] fun n : ℕ => 1 / (Real.exp n - 1) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hcount : (n.divisors.card : ℝ) = ∑ k ∈ Icc 1 n, (if k ∣ n then 1 else 0 : ℝ) := by
    rw [sum_boole, Nat.divisors, Ico_add_one_right_eq_Icc]
  simp only [one_mul, Real.norm_eq_abs, hcount, ← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans
    ((sum_abs_exp_sub_indicator_lt A hA n hn).le.trans (le_abs_self _))

/-- **Exponential approximation of the sum-of-divisors function.** Let $A$ be a real-valued
function of two natural numbers such that $A(k, n) \sin^2(n\pi/k) \ge 1$ for all natural numbers
$k, n$ with $1 \le k \le n$ and $k \nmid n$. For a natural number $n \ge 1$ let $\sigma(n)$
be the sum of the positive divisors of $n$ and
$$\tilde\sigma(n) = \sum_{k=1}^{n} k\, e^{-nkA(k, n)\sin^2(n\pi/k)}.$$
Then $\tilde\sigma(n) - \sigma(n) < \frac{n}{e^n - 1}$.

Source: Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the
Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 3
(`integers-2026-A46-thm-3`). -/
public theorem divisorSumApprox_sub_lt (A : ℕ → ℕ → ℝ)
    (hA : ∀ k n, 1 ≤ k → k ≤ n → ¬ k ∣ n →
      1 ≤ A k n * Real.sin (n * Real.pi / k) ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, k * Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2)) -
        ∑ d ∈ n.divisors, (d : ℝ) < n / (Real.exp n - 1) := by
  let w (k : ℕ) := Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2))
  let δ (k : ℕ) : ℝ := if k ∣ n then 1 else 0
  have hdiv : ∑ d ∈ n.divisors, (d : ℝ) = ∑ k ∈ Icc 1 n, k * δ k := by
    simp [Nat.divisors, Ico_add_one_right_eq_Icc, sum_filter, δ, mul_ite]
  calc
    _ = ∑ k ∈ Icc 1 n, k * (w k - δ k) := by
      rw [hdiv, ← sum_sub_distrib]
      simp only [mul_sub, w]
    _ ≤ ∑ k ∈ Icc 1 n, n * |w k - δ k| := by
      apply sum_le_sum
      intro k hk
      calc
        _ ≤ (k : ℝ) * |w k - δ k| := mul_le_mul_of_nonneg_left (le_abs_self _) k.cast_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_Icc.mp hk).2) (abs_nonneg _)
    _ = n * ∑ k ∈ Icc 1 n, |w k - δ k| := (mul_sum ..).symm
    _ < _ := by
      simpa only [mul_one_div] using
        mul_lt_mul_of_pos_left (sum_abs_exp_sub_indicator_lt A hA n hn)
          (show 0 < (n : ℝ) by exact_mod_cast (show 0 < n from hn))

end MetaMathlibExt
