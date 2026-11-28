/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Lee's identity for Stirling numbers of the second kind from higher columns

Lee's identity expresses `(n - k) * Nat.stirlingSecond n k` as a weighted sum over
higher columns of row `n`. In the Stirling recurrence, Pascal's identity turns the
difference of successive binomial weights into a telescoping sum.
-/

open Finset

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

/-- The weight for column `k + r + 1`, with the summation index shifted by two. -/
private def columnWeight (k r : ℕ) : ℤ :=
  r.factorial * (-1 : ℤ) ^ r * (k + r + 1).choose (r + 2)

/-- Extend the column sum to a common cutoff so that the recurrence uses the same
range for adjacent columns. Entries above the diagonal vanish. -/
private theorem sum_columnWeight (n k N : ℕ) (hn : n ≤ k + N) :
    (∑ r ∈ range N, columnWeight k r * Nat.stirlingSecond n (k + r + 1)) =
      ((n : ℤ) - k) * Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero =>
    simp only [Nat.stirlingSecond_zero_succ, Nat.cast_zero, mul_zero, sum_const_zero]
    cases k <;> simp
  | succ n ih =>
    cases k with
    | zero =>
      simp [columnWeight]
    | succ k =>
      let boundary (r : ℕ) : ℤ :=
        r.factorial * (-1 : ℤ) ^ r * (k + r + 1).choose (r + 1) *
          Nat.stirlingSecond n (k + r + 1)
      have step (r : ℕ) :
          columnWeight (k + 1) r * Nat.stirlingSecond (n + 1) (k + 1 + r + 1) =
            (k + 1 : ℤ) * (columnWeight (k + 1) r * Nat.stirlingSecond n (k + 1 + r + 1)) +
              columnWeight k r * Nat.stirlingSecond n (k + r + 1) +
              (boundary r - boundary (r + 1)) := by
        simp only [boundary, columnWeight, Nat.succ_add, Nat.add_succ,
          Nat.stirlingSecond_succ_succ n, Nat.cast_mul, Nat.cast_add,
          Nat.factorial_succ r, pow_succ (-1 : ℤ) r]
        rw [Nat.choose_succ_succ' (k + r + 1) (r + 1), Nat.cast_add]
        push_cast
        ring
      have htop : boundary N = 0 := by
        simp [boundary, Nat.stirlingSecond_eq_zero_of_lt (show n < k + N + 1 by omega)]
      simp_rw [step]
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_range_sub', htop,
        ih (k + 1) (by omega), ih k (by omega), Nat.stirlingSecond_succ_succ]
      simp [boundary, Nat.cast_add, Nat.cast_mul]
      ring

/-- **Lee's identity for Stirling numbers of the second kind from higher columns.** Write
$S(n, k)$ for the Stirling number of the second kind, the number of partitions of an $n$-element
set into $k$ nonempty blocks. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$,
the following identity of integers holds:
$$(n - k)\, S(n, k) = \sum_{j=2}^{n-k+1} (j-2)!\, (-1)^j \binom{k+j-1}{j}\, S(n, k+j-1).$$

This is Lee's Theorem 8 with the denominator $n - k$ cleared and the generalized binomial
coefficient written as $\binom{-k}{j} = (-1)^j \binom{k+j-1}{j}$.

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 8
(TeX label `thm:dwdwf`). -/
public theorem stirlingSecond_mul_sub_eq_sum_factorial_negChoose
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ((n : ℤ) - k) * (Nat.stirlingSecond n k : ℤ) =
      ∑ j ∈ Finset.Icc 2 (n - k + 1),
        (Nat.factorial (j - 2) : ℤ) *
          ((-1 : ℤ) ^ j * (Nat.choose (k + j - 1) j : ℤ)) *
          (Nat.stirlingSecond n (k + j - 1) : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
    ← sum_columnWeight n (k + 1) (n - (k + 1)) (by omega)]
  simp only [Nat.succ_add_sub_one]
  apply sum_congr rfl
  intro r _
  rw [add_comm 2 r, Nat.add_sub_cancel, pow_add]
  simp only [columnWeight, Nat.succ_add, Nat.add_succ]
  ring

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted
