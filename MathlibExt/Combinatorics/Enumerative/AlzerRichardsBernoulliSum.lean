/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.Choose.Cast
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Alternating Stirling sums for Bernoulli numbers

The Alzer–Richards sum of normalized Stirling numbers of the second kind gives the Bernoulli
number through degree `n`, with an explicit correction in degree `n + 1`.
-/

namespace MetaMathlibExt

open Finset PowerSeries

namespace sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli

-- The series (exp(X) - 1) / X has constant term 1 and linear coefficient 1/2.
private noncomputable def expTail : PowerSeries ℚ :=
  mk fun i => coeff (i + 1) (exp ℚ)

private theorem expTail_mul_X : expTail * X = exp ℚ - 1 := by
  simpa [expTail] using (sub_const_eq_shift_mul_X (exp ℚ)).symm

-- Expand (exp(X) - 1)^k by the binomial theorem. Its coefficient in degree r + k
-- is the alternating power sum for S(r+k,k), divided by (r+k)!.
private theorem factorial_mul_coeff_expTail_pow (r k : ℕ) :
    (r.factorial : ℚ) * coeff r (expTail ^ k) =
      (Nat.stirlingSecond (r + k) k : ℚ) / ((r + k).choose k : ℚ) := by
  have h : (Nat.stirlingSecond (r + k) k : ℚ) * k.factorial =
      ∑ j ∈ range (k + 1), (-1 : ℚ) ^ (k - j) * k.choose j * (j : ℚ) ^ (r + k) := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact stirlingSecond_mul_factorial_eq_sum (r + k) k
  have hc : coeff (r + k) ((exp ℚ - 1) ^ k) =
      (Nat.stirlingSecond (r + k) k : ℚ) * k.factorial / (r + k).factorial := by
    rw [show exp ℚ - 1 = exp ℚ + C (-1 : ℚ) by simp [sub_eq_add_neg],
      add_pow, map_sum, h, sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [coeff_mul_natCast, ← map_pow, coeff_mul_C, exp_pow_eq_rescale_exp, coeff_rescale,
      coeff_exp]
    simp
    ring
  rw [← expTail_mul_X, mul_pow, coeff_mul_X_pow] at hc
  rw [hc, Nat.cast_choose ℚ (Nat.le_add_left k r), Nat.add_sub_cancel]
  field_simp

-- Multiplying the shifted binomial sum by expTail restores the missing constant term
-- in the binomial expansion of (1 - expTail)^(n+1).
private theorem binomial_series (n : ℕ) :
    ∑ k ∈ range (n + 1), (-expTail) ^ k * ((n + 1).choose (k + 1) : ℕ) =
      bernoulliPowerSeries ℚ - bernoulliPowerSeries ℚ * (1 - expTail) ^ (n + 1) := by
  have hB : bernoulliPowerSeries ℚ * expTail = 1 := by
    apply mul_right_cancel₀ (X_ne_zero (R := ℚ))
    rw [one_mul, mul_assoc, expTail_mul_X, bernoulliPowerSeries_mul_exp_sub_one]
  have hbin : (1 - expTail) ^ (n + 1) =
      (∑ k ∈ range (n + 1), (-expTail) ^ k * ((n + 1).choose (k + 1) : ℕ)) *
        (-expTail) + 1 := by
    rw [show 1 - expTail = -expTail + 1 by ring, add_pow, sum_range_succ', sum_mul]
    simp [pow_succ, mul_right_comm]
  rw [hbin]
  linear_combination
    -(∑ k ∈ range (n + 1), (-expTail) ^ k * ((n + 1).choose (k + 1) : ℕ)) * hB

private theorem sum_eq_coeff (n r : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k *
        (((n + 1).choose (k + 1) : ℚ) / ((r + k).choose k : ℚ)) *
          (Nat.stirlingSecond (r + k) k : ℚ) =
      (r.factorial : ℚ) * coeff r
        (bernoulliPowerSeries ℚ - bernoulliPowerSeries ℚ * (1 - expTail) ^ (n + 1)) := by
  rw [← binomial_series, map_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hsign : (-expTail) ^ k = C ((-1 : ℚ) ^ k) * expTail ^ k := by
    rw [map_pow, map_neg, map_one, neg_eq_neg_one_mul expTail, mul_pow]
  rw [hsign, coeff_mul_natCast, coeff_C_mul]
  linear_combination
    -((-1 : ℚ) ^ k * (n + 1).choose (k + 1)) * factorial_mul_coeff_expTail_pow r k

end sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli

open sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli in
/-- **Alternating Stirling sums with $\binom{n+1}{k+1}$ give Bernoulli numbers.** Write $S(n, k)$
for the Stirling numbers of the second kind and $B_n$ for the Bernoulli numbers, with
$B_1 = -1/2$. Let $n$ be a natural number. Then for every natural number $r \le n$,
$$
\sum_{k=0}^{n} (-1)^k \frac{\binom{n+1}{k+1}}{\binom{r+k}{k}} S(r+k, k) = B_r,
$$
and
$$
\sum_{k=0}^{n} (-1)^k \frac{\binom{n+1}{k+1}}{\binom{n+1+k}{k}} S(n+1+k, k) =
B_{n+1} - (-1/2)^{n+1} (n+1)!.
$$

The case $r = n$ is Muthumalai's formula.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 2, Equation (4). -/
public theorem sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli (n : ℕ) :
    (∀ r ≤ n, ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k *
        (((n + 1).choose (k + 1) : ℚ) / ((r + k).choose k : ℚ)) *
          (Nat.stirlingSecond (r + k) k : ℚ) = bernoulli r) ∧
      ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k *
          (((n + 1).choose (k + 1) : ℚ) / ((n + 1 + k).choose k : ℚ)) *
            (Nat.stirlingSecond (n + 1 + k) k : ℚ) =
        bernoulli (n + 1) - (-1 / 2 : ℚ) ^ (n + 1) * ((n + 1).factorial : ℚ) := by
  let g : PowerSeries ℚ := mk fun i => coeff (i + 1) (1 - expTail)
  have hshift : 1 - expTail = g * X := by
    have hzero : constantCoeff (1 - expTail) = 0 := by
      rw [map_sub, map_one]
      norm_num [expTail, coeff_exp]
    calc
      1 - expTail = g * X + C (constantCoeff (1 - expTail)) := eq_shift_mul_X_add_const _
      _ = g * X := by rw [hzero, map_zero, add_zero]
  have hg : constantCoeff g = -1 / 2 := by norm_num [g, expTail, coeff_exp, Nat.factorial]
  have hfactor : bernoulliPowerSeries ℚ * (1 - expTail) ^ (n + 1) =
      (bernoulliPowerSeries ℚ * g ^ (n + 1)) * X ^ (n + 1) := by
    rw [hshift, mul_pow, mul_assoc]
  have hcoeff (r : ℕ) : (r.factorial : ℚ) * coeff r (bernoulliPowerSeries ℚ) =
      bernoulli r := by
    simp [bernoulliPowerSeries]
    field_simp
  constructor
  · intro r hr
    rw [sum_eq_coeff, hfactor, map_sub, coeff_mul_X_pow', ite_eq_right (by omega), sub_zero, hcoeff]
  · rw [sum_eq_coeff, hfactor, map_sub, coeff_mul_X_pow', ite_eq_left le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, hg, mul_sub, hcoeff]
    simp [bernoulliPowerSeries, mul_comm]

end MetaMathlibExt
