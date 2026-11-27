/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The factor $hat C(k)$ is below $1.525$

This module proves `exp_five_div_log_bound_lt`: for every natural number $k ge 13042$,
with $L^-(k) = (k+1)(log(k+1) + loglog(k+1) - 1)$,
$hat C(k) = exp(5/log L^-(k)) < 1.525$.

The proof bounds $log 13043$, $loglog 13043$, $log L^-(13042)$ and $log 1.525$ from
below with Taylor remainders for $log(1-x)$ around nearby $2$-$3$-$5$-smooth numbers,
using Mathlib's bounds on $log 2$, $log 3$ and $log 5$. Monotonicity of
$x mapsto x(log x + loglog x - 1)$ extends the bound at $k = 13042$ to all larger $k$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 5
(`integers-2026-A86-lem-5`).
-/

namespace MetaMathlibExt

@[expose] public section

open Real

private lemma log13043_gt : (9.476 : ℝ) < log 13043 := by
  have h13122 : (13043 : ℝ) = 13122 * (1 - 79 / 13122) := by norm_num
  have hpos1 : (0 : ℝ) < 13122 := by norm_num
  have hpos2 : (0 : ℝ) < 1 - 79 / 13122 := by norm_num
  have hlog : log 13043 = log 13122 + log (1 - 79 / 13122) := by
    rw [h13122, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
  have h13122eq : (13122 : ℝ) = 2 * 3 ^ 8 := by norm_num
  have hlog13122 : log 13122 = log 2 + 8 * log 3 := by
    rw [h13122eq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hTaylor := Real.abs_log_sub_add_sum_range_le (x := (79 / 13122 : ℝ)) (by norm_num) 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hTaylor
  simp only [Nat.cast_zero, zero_add, pow_one, Nat.cast_one] at hTaylor
  rw [abs_le] at hTaylor
  have habs : |(79 / 13122 : ℝ)| = 79 / 13122 := by norm_num
  rw [habs] at hTaylor
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  rw [hlog, hlog13122]
  linarith [hTaylor.1, h2, h3]

private lemma log9476_gt : (2.2487 : ℝ) < log 9.476 := by
  have h9 : (9.476 : ℝ) = 48 / 5 * (1 - 31 / 2400) := by norm_num
  have hpos1 : (0 : ℝ) < 48 / 5 := by norm_num
  have hpos2 : (0 : ℝ) < 1 - 31 / 2400 := by norm_num
  have hlog : log 9.476 = log (48 / 5) + log (1 - 31 / 2400) := by
    rw [h9, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
  have h48eq : (48 / 5 : ℝ) = 2 ^ 4 * 3 / 5 := by norm_num
  have hlog48 : log (48 / 5) = 4 * log 2 + log 3 - log 5 := by
    rw [h48eq, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  have hTaylor := Real.abs_log_sub_add_sum_range_le (x := (31 / 2400 : ℝ)) (by norm_num) 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hTaylor
  simp only [Nat.cast_zero, zero_add, pow_one, Nat.cast_one] at hTaylor
  rw [abs_le] at hTaylor
  have habs : |(31 / 2400 : ℝ)| = 31 / 2400 := by norm_num
  rw [habs] at hTaylor
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have h5 := Real.log_five_lt_d9
  rw [hlog, hlog48]
  linarith [hTaylor.1, h2, h3, h5]

private lemma loglog13043_gt : (2.2487 : ℝ) < log (log 13043) := by
  have h1 : (9.476 : ℝ) < log 13043 := log13043_gt
  have h2 : (2.2487 : ℝ) < log 9.476 := log9476_gt
  have hle : log 9.476 ≤ log (log 13043) := Real.log_le_log (by norm_num) (le_of_lt h1)
  linarith

private lemma L0_gt : (139882 : ℝ) < 13043 * (log 13043 + log (log 13043) - 1) := by
  have ha := log13043_gt
  have hb := loglog13043_gt
  have hpos : (0 : ℝ) < 13043 := by norm_num
  have hmul : (13043 : ℝ) * 10.7247 < 13043 * (log 13043 + log (log 13043) - 1) := by
    apply mul_lt_mul_of_pos_left _ hpos
    linarith
  have hnum : (139882 : ℝ) < 13043 * 10.7247 := by norm_num
  linarith

private lemma log139882_gt : (11.84854 : ℝ) < log 139882 := by
  have h9 : (139882 : ℝ) = 139968 * (1 - 43 / 69984) := by norm_num
  have hpos1 : (0 : ℝ) < 139968 := by norm_num
  have hpos2 : (0 : ℝ) < 1 - 43 / 69984 := by norm_num
  have hlog : log 139882 = log 139968 + log (1 - 43 / 69984) := by
    rw [h9, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
  have hCeq : (139968 : ℝ) = 2 ^ 6 * 3 ^ 7 := by norm_num
  have hlogC : log 139968 = 6 * log 2 + 7 * log 3 := by
    rw [hCeq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    ring
  have hTaylor := Real.abs_log_sub_add_sum_range_le (x := (43 / 69984 : ℝ)) (by norm_num) 1
  rw [Finset.sum_range_succ, Finset.sum_range_zero] at hTaylor
  simp only [Nat.cast_zero, zero_add, pow_one] at hTaylor
  rw [abs_le] at hTaylor
  have habs : |(43 / 69984 : ℝ)| = 43 / 69984 := by norm_num
  rw [habs] at hTaylor
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  rw [hlog, hlogC]
  linarith [hTaylor.1, h2, h3]

private lemma logL0_gt :
    (11.84854 : ℝ) < log (13043 * (log 13043 + log (log 13043) - 1)) := by
  have h1 : (139882 : ℝ) < 13043 * (log 13043 + log (log 13043) - 1) := L0_gt
  have h2 : (11.84854 : ℝ) < log 139882 := log139882_gt
  have hle : log 139882 ≤ log (13043 * (log 13043 + log (log 13043) - 1)) :=
    Real.log_le_log (by norm_num) (le_of_lt h1)
  linarith

private lemma log1525_gt : (0.421994 : ℝ) < log 1.525 := by
  have h9 : (1.525 : ℝ) = 61 / 40 := by norm_num
  have h61 : (61 : ℝ) = 64 * (1 - 3 / 64) := by norm_num
  have hlog : log 1.525 = log 61 - log 40 := by
    rw [h9, Real.log_div (by norm_num) (by norm_num)]
  have hlog61 : log 61 = 6 * log 2 + log (1 - 3 / 64) := by
    have hpos1 : (0 : ℝ) < 64 := by norm_num
    have hpos2 : (0 : ℝ) < 1 - 3 / 64 := by norm_num
    have hmul : log 61 = log 64 + log (1 - 3 / 64) := by
      rw [h61, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
    have h64 : log (64 : ℝ) = 6 * log 2 := by
      have heq : (64 : ℝ) = 2 ^ 6 := by norm_num
      rw [heq, Real.log_pow]
      norm_num
    rw [hmul, h64]
  have hlog40 : log 40 = 3 * log 2 + log 5 := by
    have heq : (40 : ℝ) = 2 ^ 3 * 5 := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  have hTaylor := Real.abs_log_sub_add_sum_range_le (x := (3 / 64 : ℝ)) (by norm_num) 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at hTaylor
  simp only [Nat.cast_zero, zero_add, pow_one, Nat.cast_one, Nat.cast_ofNat] at hTaylor
  rw [abs_le] at hTaylor
  have habs : |(3 / 64 : ℝ)| = 3 / 64 := by norm_num
  rw [habs] at hTaylor
  have h2 := Real.log_two_gt_d9
  have h5 := Real.log_five_lt_d9
  rw [hlog, hlog61, hlog40]
  linarith [hTaylor.1, h2, h5]

private lemma base_case :
    exp (5 / log (13043 * (log 13043 + log (log 13043) - 1))) < 1.525 := by
  have hL := logL0_gt
  have hM := log1525_gt
  have hLpos : (0 : ℝ) < log (13043 * (log 13043 + log (log 13043) - 1)) := by linarith
  have hmul : (11.84854 : ℝ) * 0.421994
      < log (13043 * (log 13043 + log (log 13043) - 1)) * log 1.525 := by
    apply mul_lt_mul'' hL hM (by norm_num) (by linarith)
  have hnum : (5 : ℝ) < 11.84854 * 0.421994 := by norm_num
  have hprod : (5 : ℝ) < log (13043 * (log 13043 + log (log 13043) - 1)) * log 1.525 := by
    linarith
  have hdiv : (5 : ℝ) / log (13043 * (log 13043 + log (log 13043) - 1)) < log 1.525 := by
    rw [div_lt_iff₀ hLpos]
    linarith [hprod]
  have hpos : (0 : ℝ) < 1.525 := by norm_num
  exact (Real.lt_log_iff_exp_lt hpos).mp hdiv

private lemma L_mono (k : ℕ) (hk : 13042 ≤ k) :
    (13043 : ℝ) * (log 13043 + log (log 13043) - 1)
      ≤ ((k : ℝ) + 1) * (log ((k : ℝ) + 1) + log (log ((k : ℝ) + 1)) - 1) := by
  have hx : (13043 : ℝ) ≤ (k : ℝ) + 1 := by
    have hcast : (13042 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hxpos : (0 : ℝ) < (13043 : ℝ) := by norm_num
  have hlog1 : log 13043 ≤ log ((k : ℝ) + 1) := Real.log_le_log hxpos hx
  have hlog13043pos : (0 : ℝ) < log 13043 := by
    have hbound := log13043_gt
    linarith
  have hlog2 : log (log 13043) ≤ log (log ((k : ℝ) + 1)) :=
    Real.log_le_log hlog13043pos hlog1
  have hg : log 13043 + log (log 13043) - 1
      ≤ log ((k : ℝ) + 1) + log (log ((k : ℝ) + 1)) - 1 := by
    linarith
  have hgpos : (0 : ℝ) ≤ log 13043 + log (log 13043) - 1 := by
    have ha := log13043_gt
    have hb := loglog13043_gt
    linarith
  have hxnonneg : (0 : ℝ) ≤ (k : ℝ) + 1 := by
    have hcast : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact mul_le_mul hx hg hgpos hxnonneg

/-- **The factor $\hat C(k)$ is below $1.525$.** Let $\log$ be the natural logarithm. For every
natural number $k \ge 13042$, with $L^-(k) = (k+1)(\log(k+1) + \log\log(k+1) - 1)$,
$$\hat C(k) = \exp\Bigl(\frac{5}{\log L^-(k)}\Bigr) < 1.525.$$

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Lemma 5
(`integers-2026-A86-lem-5`). -/
public theorem exp_five_div_log_bound_lt (k : ℕ) (hk : 13042 ≤ k) :
    exp (5 / log ((k + 1 : ℝ) * (log (k + 1) + log (log (k + 1)) - 1))) < 1.525 := by
  have hmono := L_mono k hk
  have hL0pos : (0 : ℝ) < (13043 : ℝ) * (log 13043 + log (log 13043) - 1) := by
    have hbound := L0_gt
    linarith
  have hlogle : log ((13043 : ℝ) * (log 13043 + log (log 13043) - 1))
      ≤ log (((k : ℝ) + 1) * (log ((k : ℝ) + 1) + log (log ((k : ℝ) + 1)) - 1)) :=
    Real.log_le_log hL0pos hmono
  have hlog0pos : (0 : ℝ) < log ((13043 : ℝ) * (log 13043 + log (log 13043) - 1)) := by
    have hbound := logL0_gt
    linarith
  have hdivle : (5 : ℝ) / log (((k : ℝ) + 1) * (log ((k : ℝ) + 1) + log (log ((k : ℝ) + 1)) - 1))
      ≤ 5 / log ((13043 : ℝ) * (log 13043 + log (log 13043) - 1)) := by
    apply div_le_div_of_nonneg_left (by norm_num) hlog0pos hlogle
  have hexple : exp (5 / log (((k : ℝ) + 1) * (log ((k : ℝ) + 1) + log (log ((k : ℝ) + 1)) - 1)))
      ≤ exp (5 / log ((13043 : ℝ) * (log 13043 + log (log 13043) - 1))) :=
    Real.exp_le_exp.mpr hdivle
  exact lt_of_le_of_lt hexple base_case

end

end MetaMathlibExt
