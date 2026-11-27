/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehavior
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tests for log-convexity, log-concavity and reciprocal log-balancedness

The arithmetic progression `z n = n + 1` illustrates log-concavity and reciprocal log-balancedness.
A geometric progression realizes equality in log-concavity at the minimum order.
-/

namespace MetaMathlibExt

-- Both lags contribute to the order-three recurrence for the arithmetic progression.
example (n : ℕ) (hn : 1 ≤ n) :
    ((n - 1 : ℕ) + 1 : ℝ) * (↑(n + 1) + 1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
  let c (j : ℕ) : ℝ := if j = 1 then 7 / 4 else if j = 2 then 1 / 2 else 1 / 4
  apply logConcave_of_linearRecurrence_of_initial_logConcave 3 (by decide) c _
    (fun i => (i : ℝ) + 1) (by intro i; positivity) _ _ n hn
  · intro j hj hj'
    interval_cases j <;> norm_num [c]
  · intro i hi
    rw [show Finset.Icc 2 3 = {2, 3} by decide]
    norm_num [c, Nat.cast_sub (show 1 ≤ i by omega), Nat.cast_sub (show 2 ≤ i by omega),
      Nat.cast_sub hi]
    linarith
  · intro i hi hk
    interval_cases i <;> norm_num

-- At the minimum order, a zero lag coefficient gives a geometric progression.
example (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    a ^ (n - 1) * a ^ (n + 1) ≤ (a ^ n) ^ 2 := by
  apply logConcave_of_linearRecurrence_of_initial_logConcave 2 (by decide)
    (fun j => if j = 1 then a else 0) _ (fun i => a ^ i) (pow_pos ha) _ _ n hn
  · intro j hj _
    simp [show j ≠ 1 by omega]
  · intro i hi
    simp [← pow_succ', Nat.sub_add_cancel (Nat.le_of_succ_le hi)]
  · intro i hi hk
    interval_cases i
    simp

-- The strictly log-convex sequence 2^n + 1 has a nonzero lag coefficient at order two.
example (n : ℕ) (hn : 1 ≤ n) :
    ((2 : ℝ) ^ n + 1) ^ 2 ≤ (2 ^ (n - 1) + 1) * (2 ^ (n + 1) + 1) := by
  let c (j : ℕ) : ℝ := if j = 1 then 3 else 2
  apply logConvex_of_linearRecurrence_of_initial_logConvex 2 (by decide) c _
    (fun i => 2 ^ i + 1) (by intro i; positivity) _ _ n hn
  · intro j hj _
    simp [c, show j ≠ 1 by omega]
  · intro i hi
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    simp [c, pow_succ]
    linarith
  · intro i hi hk
    interval_cases i
    norm_num

example (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n + 1 : ℝ)) ^ 2 ≤ (1 / ((n - 1 : ℕ) + 1 : ℝ)) * (1 / (↑(n + 1) + 1 : ℝ)) ∧
      (1 / ((n - 1 : ℕ) + 1 : ℝ) / (n - 1).factorial) *
        (1 / (↑(n + 1) + 1 : ℝ) / (n + 1).factorial) ≤
          (1 / (n + 1 : ℝ) / n.factorial) ^ 2 := by
  apply inv_logBalanced_of_recurrence_of_initial (3 / 2) (1 / 2) (by norm_num)
    (fun i => (i : ℝ) + 1) (by intro i; positivity) _ 0 _ _ n hn
  · intro i hi
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hi, Nat.cast_ofNat]
    linarith
  · intro i hlo hhi
    interval_cases i <;> norm_num [Nat.factorial]
  · intro i _
    push_cast
    field_simp
    linarith

-- At the first covered index the three partial sums are 2, k + 4 and 3k + 7.
example (k : ℕ) (hk : 1 ≤ k) : 2 * (3 * (k : ℤ) + 7) ≤ (k + 4 : ℤ) ^ 2 := by
  convert! genLeonardo_partialSum_logConcave k hk 2 (by decide) using 1 <;>
    norm_num [Finset.sum_range_succ, genLeonardo] <;> ring

-- One index earlier the log-concavity difference is negative for every positive k.
example (k : ℕ) :
    (∑ i ∈ Finset.range 2, genLeonardo k i) ^ 2 -
      (∑ i ∈ Finset.range 1, genLeonardo k i) * (∑ i ∈ Finset.range 3, genLeonardo k i) =
        -(k : ℤ) := by
  norm_num [Finset.sum_range_succ, genLeonardo]
  ring

-- The first eligible triple for k = 1 consists of the Leonardo numbers 109, 177 and 287.
example : ((177 : ℝ) ^ (1 / 10 : ℝ)) ^ 2 ≤
    (109 : ℝ) ^ (1 / 9 : ℝ) * (287 : ℝ) ^ (1 / 11 : ℝ) := by
  have hs : Real.sqrt 57 ≤ 35 := Real.sqrt_le_iff.mpr (by norm_num)
  have h := genLeonardo_rpow_inv_logBalanced 1 le_rfl 9 le_rfl
    (by norm_num; linarith) 10 le_rfl
  exact h.1

-- For k = 29 the square-root threshold is exactly 11, so the factorial inequality starts at 12.
example :
    (genLeonardo 29 11 : ℝ) ^ (1 / 11 : ℝ) / Nat.factorial 11 *
        ((genLeonardo 29 13 : ℝ) ^ (1 / 13 : ℝ) / Nat.factorial 13) ≤
      ((genLeonardo 29 12 : ℝ) ^ (1 / 12 : ℝ) / Nat.factorial 12) ^ 2 := by
  have hs : Real.sqrt 1849 = 43 := by
    rw [show (1849 : ℝ) = 43 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  exact (genLeonardo_rpow_inv_logBalanced 29 (by decide) 11 (by decide)
    (by norm_num [hs]) 12 le_rfl).2

end MetaMathlibExt
