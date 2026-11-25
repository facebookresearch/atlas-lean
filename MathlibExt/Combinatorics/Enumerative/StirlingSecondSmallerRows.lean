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
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.LinearCombination

/-!
# Lee's identity for Stirling numbers of the second kind from smaller rows

The alternating binomial sum for a forward difference expresses a Stirling number
in terms of earlier entries of the same column.
-/

open Finset fwdDiff

namespace MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted

-- The shifted columns have forward differences at zero given by the preceding column.
private theorem fwdDiff_iter_shiftedColumn (n k : ℕ) :
    Δ_[1]^[n] (fun r : ℕ ↦ (Nat.stirlingSecond (r + 1) (k + 1) : ℤ)) 0 =
      Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero => simp [Nat.stirlingSecond_succ_succ]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases k with
    | zero =>
      simp [Nat.stirlingSecond_one_right, fwdDiff_const, fwdDiff_iter_eq_sum_shift]
    | succ k =>
      let col (k r : ℕ) : ℤ := Nat.stirlingSecond (r + 1) (k + 1)
      have step : Δ_[1] (col (k + 1)) = (k + 1) • col (k + 1) + col k := by
        funext r
        change col (k + 1) (r + 1) - col (k + 1) r = (k + 1) • col (k + 1) r + col k r
        simp only [col, Nat.stirlingSecond_succ_succ (r + 1), nsmul_eq_mul,
          Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        ring
      change Δ_[1]^[n] (Δ_[1] (col (k + 1))) 0 = _
      rw [step, fwdDiff_iter_add, fwdDiff_iter_const_smul, Pi.add_apply, Pi.smul_apply]
      simp only [col, ih, nsmul_eq_mul, Nat.stirlingSecond_succ_succ n,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- **Lee's identity for Stirling numbers of the second kind from smaller rows.** Write $S(n, k)$
for the Stirling number of the second kind, the number of partitions of an $n$-element set into
$k$ nonempty blocks. For natural numbers $k$ and $n$ with $k \ge 1$ and $n \ge k + 1$, the
following identity of integers holds:
$$(n - k)\, S(n, k) = \sum_{j=2}^{n-k+1} (-1)^j \binom{n}{j}\, S(n-j+1, k).$$

This is Lee's Theorem 4 with the denominator $n - k$ cleared.

Source: Kwankyu Lee, "Some New Identities for Stirling Numbers", Theorem 4
(TeX label `thm:mxcnd`). -/
public theorem stirlingSecond_mul_sub_eq_sum_choose_alternating
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    ((n : ℤ) - k) * (Nat.stirlingSecond n k : ℤ) =
      ∑ j ∈ Finset.Icc 2 (n - k + 1),
        (Nat.choose n j : ℤ) * (Nat.stirlingSecond (n - j + 1) k : ℤ) *
          (-1 : ℤ) ^ j := by
  let term (j : ℕ) : ℤ :=
    (n.choose j : ℤ) * Nat.stirlingSecond (n - j + 1) k * (-1) ^ j
  change _ = ∑ j ∈ Icc 2 (n - k + 1), term j
  have full : ∑ j ∈ range (n + 1), term j = Nat.stirlingSecond n (k - 1) := by
    rw [← fwdDiff_iter_shiftedColumn, fwdDiff_iter_eq_sum_shift, ← sum_range_reflect term]
    refine sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := by simpa using hj
    simp [term, Nat.choose_symm hjn, Nat.sub_sub_self hjn,
      Nat.sub_add_cancel hk, mul_comm, mul_left_comm, mul_assoc]
  have tail : ∑ j ∈ Icc 2 (n - k + 1), term j = ∑ j ∈ Ico 2 (n + 1), term j := by
    apply sum_subset
    · intro j hj
      simp only [mem_Icc, mem_Ico] at hj ⊢
      omega
    · intro j hj hout
      simp only [mem_Icc, mem_Ico] at hj hout
      simp [term, Nat.stirlingSecond_eq_zero_of_lt (show n - j + 1 < k by omega)]
  rw [← sum_range_add_sum_Ico term (show 2 ≤ n + 1 by omega), ← tail,
    sum_range_succ, sum_range_one] at full
  have hrec := Nat.stirlingSecond_succ_left n k (by omega)
  simp only [term, Nat.choose_zero_right, Nat.choose_one_right, Nat.sub_zero, Nat.cast_one,
    one_mul, pow_zero, mul_one, pow_one, mul_neg_one, Nat.sub_add_cancel (by omega : 1 ≤ n),
    hrec, Nat.cast_add, Nat.cast_mul] at full
  linear_combination -full

end MathlibExt.Combinatorics.Enumerative.StirlingIdentitiesWanted
