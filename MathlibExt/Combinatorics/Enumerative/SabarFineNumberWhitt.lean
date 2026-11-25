/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.WhittGeneralizedCatalan
public import MathlibExt.Combinatorics.FineNumber
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Fine numbers from Whitt's generalized Catalan numbers

We prove Sabar's identity expressing Fine numbers in terms of Whitt's generalized Catalan
numbers at parameter two by splitting a weighted binomial sum at its midpoint.
-/

namespace MetaMathlibExt

namespace two_pow_mul_fineNumber_eq_whittGeneralizedCatalan

-- Consecutive differences in binomial row `r`, with the left endpoint padded by zero.
private def chooseDiff (r : ℕ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => (r.choose (k + 1) : ℚ) - r.choose k

private lemma chooseDiff_eq (r k : ℕ) :
    chooseDiff r k = 2 * (r.choose k : ℚ) - (r + 1).choose k := by
  cases k with
  | zero => norm_num [chooseDiff]
  | succ k => simp only [chooseDiff, Nat.choose_succ_succ, Nat.cast_add]; ring

private lemma chooseDiff_succ_succ (r k : ℕ) :
    chooseDiff (r + 1) (k + 1) = chooseDiff r (k + 1) + chooseDiff r k := by
  simp only [chooseDiff_eq, Nat.choose_succ_succ, Nat.cast_add]
  ring

private lemma cast_choose_mul_succ (r k : ℕ) (hk : k ≤ r + 1) :
    (r.choose k : ℚ) * (r + 1) = ((r + 1).choose k : ℚ) * ((r : ℚ) + 1 - k) := by
  exact_mod_cast (show r.choose k * (r + 1) = (r + 1).choose k * (r + 1 - k) from
    Nat.choose_mul_succ_eq r k)

private def weightedSum (r m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), (-2 : ℚ) ^ k * chooseDiff r k

-- Pascal's identity cancels the interior after changing the sign of the previous sum.
private lemma weightedSum_succ_succ (r m : ℕ) :
    weightedSum (r + 1) (m + 1) =
      -weightedSum r m + (-2 : ℚ) ^ (m + 1) * chooseDiff r (m + 1) := by
  have h : weightedSum (r + 1) (m + 1) =
      weightedSum r (m + 1) + (-2) * weightedSum r m := by
    have hzero (r : ℕ) : chooseDiff r 0 = 1 := rfl
    simp only [weightedSum, Finset.sum_range_succ' _ (m + 1), chooseDiff_succ_succ, pow_succ',
      mul_assoc, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, pow_zero, hzero, one_mul]
    ring
  rw [h, weightedSum, Finset.sum_range_succ _ (m + 1)]
  change weightedSum r m + _ + _ = _
  ring

private lemma whitt_sum_eq (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (2 : ℚ) ^ k * chooseDiff (n + k) k =
      (-1 : ℚ) ^ m * weightedSum (n + m + 1) m := by
  induction m with
  | zero => simp [weightedSum, chooseDiff]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, ← Nat.add_assoc, weightedSum_succ_succ]
    rw [show n + m + 1 = n + (m + 1) by omega]
    have hpow : (-1 : ℚ) ^ (m + 1) * (-2) ^ (m + 1) = 2 ^ (m + 1) := by
      rw [← mul_pow]
      norm_num
    rw [mul_add, ← mul_assoc, hpow, pow_succ (-1 : ℚ) m]
    ring

private lemma whitt_eq_weightedSum (n : ℕ) :
    whittGeneralizedCatalan 2 (n + 1) = (-1 : ℚ) ^ n * weightedSum (2 * n + 1) n := by
  rw [whittGeneralizedCatalan_succ, show 2 * n + 1 = n + n + 1 by omega, ← whitt_sum_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chooseDiff_eq]
  have h := cast_choose_mul_succ (n + k) k (by omega)
  push_cast at h
  field_simp
  linear_combination -h

private lemma fineNumber_eq_reflected_sum (n : ℕ) :
    fineNumber n =
      ∑ k ∈ Finset.range (n + 1), (-2 : ℚ) ^ (n - k) * chooseDiff (2 * n + 1) k := by
  rw [fineNumber_eq_sum, ← Finset.sum_range_reflect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk', Nat.cast_sub hk', chooseDiff_eq]
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
  have h := cast_choose_mul_succ (2 * n + 1) k (by omega)
  push_cast at h
  field_simp
  linear_combination -h

private lemma sum_chooseDiff (r : ℕ) :
    weightedSum r (r + 1) = 3 * (-1 : ℚ) ^ r := by
  have binomial (m : ℕ) :
      ∑ k ∈ Finset.range (m + 1), (-2 : ℚ) ^ k * m.choose k = (-1 : ℚ) ^ m := by
    simpa only [one_pow, mul_one, show (-2 : ℚ) + 1 = -1 by norm_num] using
      (add_pow (-2 : ℚ) 1 m).symm
  simp only [weightedSum, chooseDiff_eq, mul_sub, mul_left_comm _ (2 : ℚ),
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_succ _ (r + 1), Nat.choose_succ_self, Nat.cast_zero, mul_zero,
    add_zero, binomial, binomial, pow_succ]
  ring

private lemma chooseDiff_middle (n : ℕ) : chooseDiff (2 * n + 1) (n + 1) = 0 := by
  rw [chooseDiff, Nat.choose_symm_half, sub_self]

private lemma chooseDiff_reflect (n k : ℕ) (hk : k ≤ n) :
    chooseDiff (2 * n + 1) (2 * n + 2 - k) = -chooseDiff (2 * n + 1) k := by
  cases k with
  | zero => simp [chooseDiff]
  | succ k =>
    rw [show 2 * n + 2 - (k + 1) = (2 * n + 1 - (k + 1)) + 1 by omega, chooseDiff, chooseDiff,
      show 2 * n + 1 - (k + 1) + 1 = 2 * n + 1 - k by omega,
      Nat.choose_symm (by omega : k ≤ 2 * n + 1),
      Nat.choose_symm (by omega : k + 1 ≤ 2 * n + 1)]
    ring

private lemma weightedSum_split (n : ℕ) :
    weightedSum (2 * n + 1) (2 * n + 2) =
      weightedSum (2 * n + 1) n - (-2 : ℚ) ^ (n + 2) * fineNumber n := by
  unfold weightedSum
  rw [show 2 * n + 2 + 1 = (n + 2) + (n + 1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ _ (n + 1), chooseDiff_middle, mul_zero, add_zero,
    sub_eq_add_neg, ← Finset.sum_range_reflect (fun k =>
      (-2 : ℚ) ^ (n + 2 + k) * chooseDiff (2 * n + 1) (n + 2 + k)),
    fineNumber_eq_reflected_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hindex : n + 2 + (n - k) = 2 * n + 2 - k := by omega
  rw [Nat.add_sub_cancel, hindex, chooseDiff_reflect n k hk', ← hindex, pow_add]
  ring

end two_pow_mul_fineNumber_eq_whittGeneralizedCatalan

open two_pow_mul_fineNumber_eq_whittGeneralizedCatalan in
-- The split also applies to the row at index zero.
set_option linter.unusedVariables false in
/-- **Fine numbers from Whitt's generalized Catalan numbers.** For every natural number $n \ge 1$,
the Fine number $F(n)$, indexed so that $F(0) = 1$ and $F(1) = 0$, and Whitt's generalized Catalan
number $C(2, n+1)$ at $\alpha = 2$ satisfy

$$2^{n+2} F(n) = C(2, n+1) + 3(-1)^n.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 4 (`integers-2026-A27-cor-4`). -/
public theorem two_pow_mul_fineNumber_eq_whittGeneralizedCatalan (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 2) * fineNumber n = whittGeneralizedCatalan 2 (n + 1) + 3 * (-1) ^ n := by
  have h := (weightedSum_split n).symm.trans (sum_chooseDiff (2 * n + 1))
  rw [pow_succ (-1 : ℚ), pow_mul, neg_one_sq, one_pow, one_mul] at h
  rw [whitt_eq_weightedSum]
  have hsign : (-1 : ℚ) ^ n * (-2) ^ (n + 2) = 2 ^ (n + 2) := by
    rw [pow_add (-2 : ℚ) n, ← mul_assoc, ← mul_pow, pow_add (2 : ℚ) n]
    norm_num
  calc
    2 ^ (n + 2) * fineNumber n =
        ((-1 : ℚ) ^ n * (-2) ^ (n + 2)) * fineNumber n := by rw [hsign]
    _ = (-1 : ℚ) ^ n * weightedSum (2 * n + 1) n + 3 * (-1) ^ n := by
      linear_combination -(-1 : ℚ) ^ n * h

end MetaMathlibExt
