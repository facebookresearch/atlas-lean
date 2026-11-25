/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic.LinearCombination

/-!
# Alternating sums of signed Stirling numbers of the first kind

For every shift `j`, the alternating binomial sum of order `n + 1` of normalized signed Stirling
numbers vanishes for `r ≤ n` and equals `(n + 1)! / 2^(n + 1)` for `r = n + 1`.
-/

namespace MetaMathlibExt

open Finset PowerSeries

-- The differential equation (1 + X)L' = 1 gives the Stirling recurrence
-- for the coefficients of powers of L = log(1 + X).
private theorem factorial_mul_coeff_log_pow (n m : ℕ) :
    (n.factorial : ℚ) * coeff n (log ℚ ^ m) =
      (m.factorial : ℚ) * signedStirlingFirst n m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp
    | succ m =>
      simp [coeff_zero_eq_constantCoeff_apply, signedStirlingFirst_eq_zero_of_lt]
  | succ n ih =>
    cases m with
    | zero => simp
    | succ m =>
      have hderiv : derivative (log ℚ ^ (m + 1)) * (1 + X) =
          ((m + 1 : ℕ) : PowerSeries ℚ) * log ℚ ^ m := by
        rw [derivative_pow, Nat.add_sub_cancel, mul_assoc, derivative_log_mul_one_add_X, mul_one]
      have hshift (f : PowerSeries ℚ) :
          coeff n (derivative f * X) = coeff n f * n := by
        cases n <;> simp [coeff_succ_mul_X, coeff_derivative]
      rw [mul_add, mul_one] at hderiv
      have h := congrArg (coeff n) hderiv
      rw [map_add, hshift, coeff_derivative, coeff_natCast_mul] at h
      push_cast at h
      have hm := ih (m + 1)
      rw [signedStirlingFirst_succ_succ]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Int.cast_sub, Int.cast_mul,
        Int.cast_natCast] at hm ⊢
      linear_combination (n.factorial : ℚ) * h + (m + 1 : ℚ) * ih m - (n : ℚ) * hm

-- Removing the initial X from log(1 + X) shifts its m-th power down by m degrees.
private noncomputable def logDivX : PowerSeries ℚ :=
  mk fun n => coeff (n + 1) (log ℚ)

private theorem factorial_mul_coeff_logDivX_pow (m r : ℕ) :
    (r.factorial : ℚ) * coeff r (logDivX ^ m) =
      signedStirlingFirst (m + r) m / ((m + r).choose r : ℚ) := by
  have hlog : log ℚ = logDivX * X := by
    simpa [logDivX] using eq_shift_mul_X_add_const (log ℚ)
  have h := factorial_mul_coeff_log_pow (m + r) m
  rw [hlog, mul_pow, Nat.add_comm m r, coeff_mul_X_pow, Nat.add_comm r m] at h
  rw [Nat.cast_choose ℚ (Nat.le_add_left r m), Nat.add_sub_cancel_right, div_div_eq_mul_div,
    eq_div_iff (by positivity)]
  linear_combination (r.factorial : ℚ) * h

private theorem alternating_sum_coeff (j d r : ℕ) :
    ∑ k ∈ range (d + 1), (-1 : ℚ) ^ k *
        ((d.choose k : ℚ) / ((k + j + r).choose r : ℚ)) *
          (signedStirlingFirst (k + j + r) (k + j) : ℚ) =
      (r.factorial : ℚ) * coeff r ((1 - logDivX) ^ d * logDivX ^ j) := by
  rw [show 1 - logDivX = -logDivX + 1 by ring, add_pow, sum_mul, map_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hterm : (-logDivX) ^ k * 1 ^ (d - k) * (d.choose k : ℕ) * logDivX ^ j =
      C ((-1 : ℚ) ^ k) * logDivX ^ (k + j) * (d.choose k : ℕ) := by
    rw [map_pow, map_neg, map_one, pow_add, neg_eq_neg_one_mul logDivX, mul_pow, one_pow]
    ring
  rw [hterm, coeff_mul_natCast, coeff_C_mul]
  linear_combination -((-1 : ℚ) ^ k * d.choose k) * factorial_mul_coeff_logDivX_pow (k + j) r

/-- **Alternating sums of signed Stirling numbers of the first kind.** Write $s(n, k)$ for the
signed Stirling numbers of the first kind. For all natural numbers $j$ and $n$ and every natural
number $r \le n$,
$$
\sum_{k=0}^{n+1} (-1)^k \frac{\binom{n+1}{k}}{\binom{k+j+r}{r}} s(k+j+r, k+j) = 0,
$$
and
$$
\sum_{k=0}^{n+1} (-1)^k \frac{\binom{n+1}{k}}{\binom{k+j+n+1}{n+1}} s(k+j+n+1, k+j) =
\frac{(n+1)!}{2^{n+1}}.
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 5, Equation (7). -/
public theorem sum_choose_div_choose_mul_signedStirlingFirst (j n : ℕ) :
    (∀ r ≤ n, ∑ k ∈ range (n + 2), (-1 : ℚ) ^ k *
        (((n + 1).choose k : ℚ) / ((k + j + r).choose r : ℚ)) *
          (signedStirlingFirst (k + j + r) (k + j) : ℚ) = 0) ∧
      ∑ k ∈ range (n + 2), (-1 : ℚ) ^ k *
          (((n + 1).choose k : ℚ) / ((k + j + n + 1).choose (n + 1) : ℚ)) *
            (signedStirlingFirst (k + j + n + 1) (k + j) : ℚ) =
        ((n + 1).factorial : ℚ) / 2 ^ (n + 1) := by
  have hc : constantCoeff logDivX = 1 := by simp [logDivX]
  let g : PowerSeries ℚ := mk fun i => coeff (i + 1) (1 - logDivX)
  have hg : 1 - logDivX = g * X := by
    have hconst : constantCoeff (1 - logDivX) = 0 := by rw [map_sub, map_one, hc, sub_self]
    calc
      1 - logDivX = g * X + C (constantCoeff (1 - logDivX)) := eq_shift_mul_X_add_const _
      _ = g * X := by rw [hconst, map_zero, add_zero]
  have hg₀ : constantCoeff g = 1 / 2 := by norm_num [g, logDivX]
  have hfactor (d : ℕ) :
      (1 - logDivX) ^ d * logDivX ^ j = (g ^ d * logDivX ^ j) * X ^ d := by
    rw [hg, mul_pow]
    ring
  constructor
  · intro r hr
    rw [alternating_sum_coeff, hfactor, coeff_mul_X_pow', ite_eq_right (by omega), mul_zero]
  · simp_rw [Nat.add_assoc (_ + j) n 1]
    rw [alternating_sum_coeff, hfactor, coeff_mul_X_pow', ite_eq_left le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply]
    simp [hg₀, hc, div_eq_mul_inv]

end MetaMathlibExt
