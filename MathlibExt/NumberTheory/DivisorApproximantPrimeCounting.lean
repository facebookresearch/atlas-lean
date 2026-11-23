/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Divisors

/-!
# Exponential approximation of the divisor-counting function

The exponential weights equal one on the divisors. The total contribution of the
nondivisors is bounded by a geometric sum with ratio $e^{-n}$.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

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
  let w (k : ℕ) := Real.exp (-(n * k * A k n * Real.sin (n * Real.pi / k) ^ 2))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from hn)
  have hcount : (n.divisors.card : ℝ) = ∑ k ∈ Icc 1 n, (if k ∣ n then 1 else 0 : ℝ) := by
    rw [sum_boole, Nat.divisors, Ico_add_one_right_eq_Icc]
  have hterm (k : ℕ) (hk : k ∈ Icc 1 n) :
      |w k - (if k ∣ n then 1 else 0)| ≤ Real.exp (-n) ^ k := by
    obtain ⟨hk₁, hkn⟩ := mem_Icc.mp hk
    split_ifs with hd
    · obtain ⟨d, hd'⟩ := hd
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have harg : (n : ℝ) * Real.pi / k = d * Real.pi := by
        rw [hd', Nat.cast_mul]
        field_simp
      simpa [w, harg, Real.sin_nat_mul_pi] using pow_nonneg (Real.exp_pos (-(n : ℝ))).le k
    · rw [sub_zero, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (hA k n hk₁ hkn hd)
        (show 0 ≤ (n : ℝ) * k by positivity)
      linarith only [h]
  have hlt : Real.exp (-n) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hn')
  change ‖∑ k ∈ Icc 1 n, w k - (n.divisors.card : ℝ)‖ ≤ 1 * ‖1 / (Real.exp n - 1)‖
  rw [one_mul, Real.norm_eq_abs, hcount, ← sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Icc 1 n, |w k - (if k ∣ n then 1 else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 1 n, Real.exp (-n) ^ k := sum_le_sum hterm
    _ ≤ Real.exp (-n) / (1 - Real.exp (-n)) := by
      simpa only [Ico_add_one_right_eq_Icc, pow_one] using
        (geom_sum_Ico_le_of_lt_one (m := 1) (n := n + 1) (Real.exp_pos _).le hlt)
    _ = 1 / (Real.exp n - 1) := by
      rw [Real.exp_neg]
      field_simp
    _ ≤ _ := le_abs_self _

end MetaMathlibExt
