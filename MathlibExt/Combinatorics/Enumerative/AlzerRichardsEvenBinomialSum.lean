/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination

/-!
# The even Alzer–Richards binomial sum

Vandermonde's identity evaluates the sum as a product of two binomial coefficients,
giving closed forms at both regular and exceptional arguments.
-/

namespace MetaMathlibExt

open Finset

namespace sum_choose_mul_choose_div_choose_of_even

private lemma choose_step (z : ℂ) (k : ℕ) :
    ((k : ℂ) + 1) * Ring.choose z (k + 1) = z * Ring.choose (z - 1) k := by
  simpa [nsmul_eq_mul, Ring.choose_one_right] using
    Ring.choose_smul_choose z (n := k + 1) (k := 1) (by omega)

-- Splitting the factors of (2(t+k))! into even and odd factors evaluates the half-integer weight.
private lemma half_choose (t k : ℕ) :
    (4 : ℂ) ^ k * Ring.choose ((t : ℂ) + k - 1 / 2) k * k.factorial *
        (t + k).factorial * (2 * t).factorial = (2 * (t + k)).factorial * (t.factorial : ℂ) := by
  induction k with
  | zero => simp [mul_comm]
  | succ k ih =>
    have h := choose_step ((t : ℂ) + (k + 1) - 1 / 2) k
    rw [show (t : ℂ) + (k + 1) - 1 / 2 - 1 = t + k - 1 / 2 by ring] at h
    rw [Nat.add_succ t k, show 2 * (t + k + 1) = 2 * (t + k) + 1 + 1 by omega,
      Nat.factorial_succ (2 * (t + k) + 1), Nat.factorial_succ (2 * (t + k)),
      Nat.factorial_succ (t + k), Nat.factorial_succ k, pow_succ]
    push_cast
    linear_combination
      4 * (4 : ℂ) ^ k * k.factorial * (t + k + 1) * (t + k).factorial * (2 * t).factorial * h +
      (2 * (t + k : ℂ) + 2) * (2 * (t + k) + 1) * ih

-- This form pairs the weight with the two ordinary binomial coefficients in the convolution.
private lemma half_weight (n k : ℕ) (hk : k ≤ n) :
    (4 : ℂ) ^ k * Ring.choose ((n : ℂ) - 1 / 2) k =
      ((2 * n - k).choose k : ℂ) * (2 * n).choose n / (2 * n - k).choose n := by
  have h := half_choose (n - k) k
  rw [← Nat.cast_add, Nat.sub_add_cancel hk] at h
  rw [Nat.cast_choose ℂ (show k ≤ 2 * n - k by omega),
    Nat.cast_choose ℂ (show n ≤ 2 * n by omega),
    Nat.cast_choose ℂ (show n ≤ 2 * n - k by omega)]
  rw [show 2 * n - k - k = 2 * (n - k) by omega, show 2 * n - n = n by omega,
    show 2 * n - k - n = n - k by omega]
  have hf (r : ℕ) : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  generalize Ring.choose ((n : ℂ) - 1 / 2) k = c at h ⊢
  field_simp [hf]
  linear_combination h

private lemma choose_reflect (z : ℂ) (k : ℕ) :
    Ring.choose z k = (-1 : ℂ) ^ k * Ring.choose (-z + k - 1) k := by
  simpa only [neg_neg, Units.smul_def, zsmul_eq_mul, Int.coe_negOnePow_natCast,
    Int.cast_pow, Int.cast_neg, Int.cast_one] using Ring.choose_neg (-z) k

private lemma signed_weight (n k : ℕ) (hk : k ≤ n) :
    ((2 * n - k).choose k : ℂ) /
        (2 ^ (2 * k) * Ring.choose ((k : ℂ) - n - 1 / 2) k) =
      (-1 : ℂ) ^ k * (2 * n - k).choose n / (2 * n).choose n := by
  rw [choose_reflect, show -((k : ℂ) - n - 1 / 2) + k - 1 = n - 1 / 2 by ring,
    pow_mul, show (2 : ℂ) ^ 2 = 4 by norm_num, mul_left_comm, half_weight n k hk]
  have h₁ : ((2 * n - k).choose k : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show k ≤ 2 * n - k by omega)).ne'
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← inv_pow, inv_neg, inv_one]
  field_simp [h₁]

private lemma choose_neg_one (k : ℕ) : Ring.choose (-1 : ℂ) k = (-1) ^ k := by
  rw [choose_reflect, show -(-1 : ℂ) + k - 1 = k by ring, Ring.choose_natCast]
  simp

private lemma sum_eq_product (n : ℕ) (z : ℂ) :
    ∑ k ∈ range (n + 1), ((2 * n - k).choose k : ℂ) * Ring.choose z (2 * n - k) /
        (2 ^ (2 * k) * Ring.choose ((k : ℂ) - n - 1 / 2) k) =
      Ring.choose z n * Ring.choose (z - n - 1) n / (2 * n).choose n := by
  rw [show z - n - 1 = -1 + (z - n) by ring, Ring.add_choose_eq n (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum, sum_div]
  apply sum_congr rfl
  intro k hk
  have hk' := Nat.le_of_lt_succ (mem_range.mp hk)
  have h := Ring.choose_smul_choose z (show n ≤ 2 * n - k by omega)
  rw [nsmul_eq_mul, show 2 * n - k - n = n - k by omega] at h
  dsimp only
  rw [mul_div_right_comm, signed_weight n k hk', choose_neg_one]
  linear_combination (-1 : ℂ) ^ k / (2 * n).choose n * h

private lemma shift_choose (z : ℂ) {n : ℕ} (hn : 0 < n) :
    z * Ring.choose (z - 1) n = (z - n) * Ring.choose z n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := Ring.choose_succ_succ (z - 1) k
  rw [sub_add_cancel] at h
  push_cast
  linear_combination choose_step z k - z * h

end sum_choose_mul_choose_div_choose_of_even

open sum_choose_mul_choose_div_choose_of_even in
/-- **Closed form of the Alzer–Richards binomial sum for even $m$.** Let $m \ge 2$ be an even
integer and $x$ a complex number, and write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ for complex
$z$. Put
$$
S(x) = \sum_{k=0}^{m/2} \frac{\binom{m-k}{k} \binom{m+x}{m-k}}{2^{2k} \binom{k-m/2-1/2}{k}}.
$$
If $x \ne -m/2$, then $S(x) = \frac{x}{x+m/2} \binom{x+m}{m}$; if $x = -m/2$, then
$S(x) = \frac{(-1)^{m/2}}{2^m \binom{(m-1)/2}{m/2}}$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Corollary 2 (i), Equation (19). -/
public theorem sum_choose_mul_choose_div_choose_of_even {m : ℕ} (hm : 2 ≤ m) (hme : Even m)
    (x : ℂ) :
    (x ≠ -(m : ℂ) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m / 2 - 1 / 2) k) =
        x / (x + m / 2) * Ring.choose (x + m) m) ∧
    (x = -(m : ℂ) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m / 2 - 1 / 2) k) =
        (-1 : ℂ) ^ (m / 2) / (2 ^ m * Ring.choose (((m : ℂ) - 1) / 2) (m / 2))) := by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hme
  have hn : 0 < n := by omega
  simp only [show 2 * n / 2 = n by omega, Nat.cast_mul, Nat.cast_ofNat,
    show (2 * (n : ℂ)) / 2 = n by ring, show -(2 * (n : ℂ)) / 2 = -n by ring,
    sum_eq_product]
  constructor
  · intro hx
    have hsplit := Ring.choose_smul_choose (x + 2 * n) (show n ≤ 2 * n by omega)
    rw [nsmul_eq_mul, show 2 * n - n = n by omega,
      show x + 2 * n - n = x + n by ring] at hsplit
    have hs := shift_choose (x + n) hn
    rw [add_sub_cancel_right] at hs
    have hxn : x + n ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hx
    have hc : ((2 * n).choose n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (show n ≤ 2 * n by omega)).ne'
    rw [add_comm (2 * (n : ℂ)) x, show x + 2 * n - n = x + n by ring]
    field_simp [hxn, hc]
    linear_combination Ring.choose (x + 2 * n) n * hs - x * hsplit
  · rintro rfl
    rw [show 2 * (n : ℂ) + -n = n by ring, sub_self, zero_sub, choose_neg_one,
      Ring.choose_natCast, Nat.choose_self, Nat.cast_one, one_mul,
      show (2 * (n : ℂ) - 1) / 2 = n - 1 / 2 by ring, pow_mul,
      show (2 : ℂ) ^ 2 = 4 by norm_num, half_weight n n le_rfl,
      show 2 * n - n = n by omega, Nat.choose_self, Nat.cast_one, one_mul, div_one]

end MetaMathlibExt
