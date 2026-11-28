/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.FineNumber
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fine numbers as an alternating binomial sum

Pascal's identity reduces both formulas for twice the Fine number to a weighted partial sum
of binomial row `2 * n + 1`: three times the sum with weights `(-2) ^ (n - k)`,
minus the central entry.
-/

namespace MetaMathlibExt

namespace fineNumber_eq_half_neg_one_pow_add_sum

private def weightedSum (a : ℚ) (f : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), a ^ (m - k) * f k

private lemma weightedSum_succ (a : ℚ) (f : ℕ → ℚ) (m : ℕ) :
    weightedSum a f (m + 1) = a * weightedSum a f m + f (m + 1) := by
  simp only [weightedSum, Finset.sum_range_succ _ (m + 1), Nat.sub_self, pow_zero, one_mul,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show m + 1 - k = m - k + 1 by omega, pow_succ']
  ring

private def rowSum (r m : ℕ) : ℚ :=
  weightedSum (-2) (fun k => (r.choose k : ℚ)) m

-- Pascal's identity relates weighted partial sums in consecutive rows.
private lemma rowSum_succ_row (r m : ℕ) :
    2 * rowSum (r + 1) m = r.choose m + rowSum r m := by
  induction m with
  | zero => norm_num [rowSum, weightedSum]
  | succ m ih =>
    simp only [rowSum, weightedSum_succ, Nat.choose_succ_succ, Nat.cast_add] at *
    linear_combination -2 * ih

private lemma rowSum_succ_diagonal (r m : ℕ) :
    rowSum (r + 1) (m + 1) = r.choose (m + 1) - rowSum r m := by
  rw [rowSum, weightedSum_succ, Nat.choose_succ_succ, Nat.cast_add]
  change -2 * rowSum (r + 1) m + _ = _
  linear_combination -(rowSum_succ_row r m)

-- The factor (i + 1) / (n + 1) in the definition of the Fine number gives a difference of rows.
private lemma fineNumber_eq_rowSum (n : ℕ) :
    2 * fineNumber n = 3 * rowSum (2 * n + 1) n - (2 * n + 1).choose n := by
  let r := 2 * n + 1
  have h : fineNumber n = 2 * rowSum r n - rowSum (r + 1) n := by
    rw [fineNumber_eq_sum, ← Finset.sum_range_reflect]
    simp only [rowSum, weightedSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk', Nat.cast_sub hk']
    rw [show 2 * (n + 1) = r + 1 by dsimp [r]; omega]
    have hchoose := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_mul_succ_eq r k)
    dsimp [r] at hchoose ⊢
    push_cast [Nat.cast_sub (show k ≤ 2 * n + 1 + 1 by omega)] at hchoose
    field_simp [show (n : ℚ) + 1 ≠ 0 by positivity]
    linear_combination -hchoose
  rw [h]
  linear_combination -(rowSum_succ_row r n)

-- Along a diagonal the new term enters with positive sign and the previous terms change sign.
private lemma alternating_sum_eq_rowSum (n m : ℕ) :
    (-1 : ℚ) ^ m + weightedSum (-1)
        (fun k => (1 - (n : ℚ) / (k + 1)) * ((n + k).choose k : ℚ)) m =
      3 * rowSum (n + m + 1) m - (n + m + 1).choose (m + 1) := by
  induction m with
  | zero => simp [rowSum, weightedSum]; ring
  | succ m ih =>
    rw [weightedSum_succ, pow_succ, ← Nat.add_assoc, rowSum_succ_diagonal]
    have hterm : (1 - (n : ℚ) / (↑(m + 1) + 1)) * ((n + m + 1).choose (m + 1) : ℚ) =
        2 * ((n + m + 1).choose (m + 1) : ℚ) - ((n + m + 1 + 1).choose (m + 1 + 1) : ℚ) := by
      have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.add_one_mul_choose_eq (n + m + 1) (m + 1))
      push_cast at h ⊢
      field_simp [show (m : ℚ) + 1 + 1 ≠ 0 by positivity]
      linear_combination -h
    rw [hterm]
    linear_combination -ih

end fineNumber_eq_half_neg_one_pow_add_sum

open fineNumber_eq_half_neg_one_pow_add_sum

-- The partial sum calculation also covers the two indices below the stated bound.
set_option linter.unusedVariables false in
/-- **Fine numbers as an alternating binomial sum.** For every natural number $n \ge 2$, the Fine
number $F(n)$ satisfies
$$F(n) = \frac{1}{2} (-1)^n +
\frac{1}{2} \sum_{k=0}^{n} (-1)^{n-k} \left(1 - \frac{n}{k+1}\right) \binom{n+k}{k}.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 3 (`integers-2026-A27-cor-3`). -/
public theorem fineNumber_eq_half_neg_one_pow_add_sum (n : ℕ) (hn : 2 ≤ n) :
    fineNumber n = (1 / 2) * (-1 : ℚ) ^ n +
      (1 / 2) * ∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * (1 - (n : ℚ) / (k + 1)) * ((n + k).choose k : ℚ) := by
  have h := alternating_sum_eq_rowSum n n
  rw [← two_mul, Nat.choose_symm_of_eq_add (show 2 * n + 1 = (n + 1) + n by omega)] at h
  simp only [weightedSum, ← mul_assoc] at h
  linear_combination (fineNumber_eq_rowSum n - h) / 2

end MetaMathlibExt
