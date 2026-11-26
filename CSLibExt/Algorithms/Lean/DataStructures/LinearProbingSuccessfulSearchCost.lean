/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingInsertionCost
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Knuth's exact mean successful-search cost for linear probing

`successfulSearchCost_eq` averages the exact insertion costs by expressing each one as a
difference of consecutive weighted sums, as in Knuth's *Notes on "open" addressing*.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LinearProbing

open Finset

/-- Multiplication by the number of items extends each falling factorial by one factor. -/
private lemma mul_knuthE_zero (N k : ℕ) :
    (k : ℚ) * knuthE 0 N k =
      ∑ j ∈ range (k + 1), (k.descFactorial (j + 1) : ℚ) / (N : ℚ) ^ j := by
  cases k with
  | zero => simp
  | succ k =>
    rw [sum_range_succ, Nat.descFactorial_of_lt (Nat.lt_succ_self _)]
    simp only [Nat.cast_zero, zero_div, add_zero, knuthE, Nat.choose_zero_right,
      Nat.cast_one, one_mul, Nat.succ_sub_one, mul_sum, Nat.succ_descFactorial_succ,
      Nat.cast_mul, mul_div_assoc]

/-- The first difference of the weighted zeroth sums gives the first-order sum. -/
private lemma knuthE_one_eq_sub (N k : ℕ) :
    knuthE 1 N (k + 1) = (k + 1 : ℚ) * knuthE 0 N (k + 1) - k * knuthE 0 N k := by
  rw [mul_knuthE_zero N k]
  simp only [knuthE, Nat.add_sub_cancel, Nat.choose_one_right, Nat.choose_zero_right,
    Nat.cast_add, Nat.cast_one, one_mul, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h : (k.descFactorial j : ℚ) * k =
      k.descFactorial (j + 1) + (j : ℚ) * k.descFactorial j := by
    exact_mod_cast Nat.descFactorial_mul_self k j
  rw [← mul_div_assoc, ← sub_div]
  congr 1
  linear_combination -h

/-- **Knuth's exact mean successful-search cost for linear probing** (Knuth, *Notes on "open"
addressing*, 1963, Section 7, from Theorem 2). For `1 ≤ k ≤ N`, the average number of probes of
a successful search in a cyclic table of `N` cells holding `k` items inserted by linear probing
with independent uniform hash addresses is `T(N, k) = (1 + E_0(N, k)) / 2`, where
`E_0(N, k) = ∑_{j < k} (k - 1)(k - 2)⋯(k - j) / N ^ j`. -/
theorem successfulSearchCost_eq (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    successfulSearchCost N k = (1 + knuthE 0 N k) / 2 := by
  let total (i : ℕ) : ℚ := i * ((1 + knuthE 0 N i) / 2)
  have step (i : ℕ) (hi : i ∈ range k) : insertionCost N i = total (i + 1) - total i := by
    have h := insertionCost_eq N (i + 1) (Nat.succ_pos i) ((mem_range.mp hi).trans_le hkN)
    rw [Nat.add_sub_cancel, knuthE_one_eq_sub] at h
    rw [h]
    simp only [total, Nat.cast_add, Nat.cast_one]
    ring
  rw [successfulSearchCost, sum_congr rfl step, sum_range_sub]
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  simp [total, hk']

end Cslib.Algorithms.Lean.LinearProbing
