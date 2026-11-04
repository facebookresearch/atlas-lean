/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.IntervalCases

/-!
# Sums of antitone sequences against a profile

For a nonnegative antitone sequence `a`, `∑_{k=1}^{n-1} a k ≤ 2 ∑_{k=1}^{⌊n/2⌋} a k`; hence if
`a k ≤ θ k` on `[1, n/2]`, the sum of `a` over `[0, n)` is at most twice the sum of `θ`. These
bounds compare a sum of connection probabilities indexed by distance with the partial sums
`Σ_n` of the one-arm profile, as in revealment estimates for decision trees.

## Main results

* `StatMech.OSSS.antitone_sum_Ico_one_le_two_sum_Icc_half`.
* `StatMech.OSSS.antitone_sum_range_le_two_profile`,
  `StatMech.OSSS.antitone_sum_range_le_two_profile_strict`: comparison with a profile `θ`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech
namespace OSSS

/-- For a nonnegative antitone sequence, `∑_{k ∈ [1, n)} a k ≤ 2 ∑_{k ∈ [1, n/2]} a k`. -/
theorem antitone_sum_Ico_one_le_two_sum_Icc_half
    (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (hanti : Antitone a) (n : ℕ) :
    (∑ k ∈ Ico 1 n, a k) ≤ 2 * ∑ k ∈ Icc 1 (n / 2), a k := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      by_cases hn0 : n = 0
      · subst n
        simp
        nlinarith [ha0 1]
      rw [sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega)]
      have hhalf : (n + 2) / 2 = n / 2 + 1 := by omega
      rw [hhalf, sum_Icc_succ_top (by omega)]
      have hn : n / 2 + 1 ≤ n + 1 := by omega
      have hn' : n / 2 + 1 ≤ n := by
        omega
      have hle0 : a n ≤ a (n / 2 + 1) := hanti hn'
      have hle1 : a (n + 1) ≤ a (n / 2 + 1) := hanti hn
      nlinarith

/-- If `a k ≤ θ k` on `[1, n/2]`, then `∑_{k ∈ [1, n)} a k ≤ 2 ∑_{k < n} θ k`. -/
theorem antitone_sum_Ico_one_le_two_profile
    (a theta : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (hanti : Antitone a)
    (htheta0 : ∀ k, 0 ≤ theta k) (n : ℕ)
    (hcomp : ∀ k, k ∈ Icc 1 (n / 2) → a k ≤ theta k) :
    (∑ k ∈ Ico 1 n, a k) ≤ 2 * ∑ k ∈ range n, theta k := by
  calc
    (∑ k ∈ Ico 1 n, a k) ≤ 2 * ∑ k ∈ Icc 1 (n / 2), a k :=
      antitone_sum_Ico_one_le_two_sum_Icc_half a ha0 hanti n
    _ ≤ 2 * ∑ k ∈ Icc 1 (n / 2), theta k := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum fun k hk => hcomp k hk
    _ ≤ 2 * ∑ k ∈ range n, theta k := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [mem_Icc] at hk
        rw [mem_range]
        omega
      · intro k _ _
        exact htheta0 k

/-- If additionally `a 0 ≤ θ 0`, then `∑_{k < n} a k ≤ 2 ∑_{k < n} θ k`. -/
theorem antitone_sum_range_le_two_profile
    (a theta : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (hanti : Antitone a)
    (htheta0 : ∀ k, 0 ≤ theta k) (n : ℕ)
    (hzero : a 0 ≤ theta 0)
    (hcomp : ∀ k, k ∈ Icc 1 (n / 2) → a k ≤ theta k) :
    (∑ k ∈ range n, a k) ≤ 2 * ∑ k ∈ range n, theta k := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have htail0 := antitone_sum_Ico_one_le_two_sum_Icc_half a ha0 hanti n
    have hfirst : (∑ k ∈ Icc 1 (n / 2), a k) ≤
        ∑ k ∈ Icc 1 (n / 2), theta k :=
      sum_le_sum fun k hk => hcomp k hk
    have hsub : (∑ k ∈ Icc 1 (n / 2), theta k) ≤
        ∑ k ∈ Ico 1 n, theta k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [mem_Icc] at hk
        rw [mem_Ico]
        omega
      · intro k _ _
        exact htheta0 k
    have htail : (∑ k ∈ Ico 1 n, a k) ≤
        2 * ∑ k ∈ Ico 1 n, theta k :=
      htail0.trans <| (mul_le_mul_of_nonneg_left (hfirst.trans hsub) (by norm_num))
    have haSplit : (∑ k ∈ Ico 1 n, a k) =
        (∑ k ∈ range n, a k) - a 0 := by
      rw [sum_Ico_eq_sub a hn1]
      simp
    have hthetaSplit : (∑ k ∈ Ico 1 n, theta k) =
        (∑ k ∈ range n, theta k) - theta 0 := by
      rw [sum_Ico_eq_sub theta hn1]
      simp
    linarith [hzero, htheta0 0]

/-- Variant of `antitone_sum_range_le_two_profile` with the comparison required only for `2k < n`,
and the middle term (`2k = n`) bounded by `θ 0`. -/
theorem antitone_sum_range_le_two_profile_strict
    (a theta : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (hanti : Antitone a)
    (htheta0 : ∀ k, 0 ≤ theta k) (n : ℕ)
    (hzero : a 0 ≤ theta 0)
    (hcomp : ∀ k, k ∈ Icc 1 (n / 2) → 2 * k < n → a k ≤ theta k)
    (hmiddle : ∀ k, 2 * k = n → a k ≤ theta 0) :
    (∑ k ∈ range n, a k) ≤ 2 * ∑ k ∈ range n, theta k := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp_all
    linarith [htheta0 0]
  have hn2 : 2 ≤ n := by omega
  have haSplit : (∑ k ∈ Ico 1 n, a k) =
      (∑ k ∈ range n, a k) - a 0 := by
    rw [sum_Ico_eq_sub a (by omega : 1 ≤ n)]
    simp
  have hthetaSplit : (∑ k ∈ Ico 1 n, theta k) =
      (∑ k ∈ range n, theta k) - theta 0 := by
    rw [sum_Ico_eq_sub theta (by omega : 1 ≤ n)]
    simp
  by_cases heven : 2 * (n / 2) = n
  · let m := n / 2
    have hm : 2 * m = n := heven
    have hm1 : 1 ≤ m := by omega
    have hprev := antitone_sum_Ico_one_le_two_sum_Icc_half
      a ha0 hanti (n - 1)
    have hhalf : (n - 1) / 2 = m - 1 := by omega
    rw [hhalf] at hprev
    have hfirst : (∑ k ∈ Icc 1 (m - 1), a k) ≤
        ∑ k ∈ Icc 1 (m - 1), theta k := by
      apply sum_le_sum
      intro k hk
      apply hcomp k
      · rw [mem_Icc] at hk ⊢
        omega
      · rw [mem_Icc] at hk
        omega
    have hsub : (∑ k ∈ Icc 1 (m - 1), theta k) ≤
        ∑ k ∈ Ico 1 n, theta k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [mem_Icc] at hk
        rw [mem_Ico]
        omega
      · intro k _ _
        exact htheta0 k
    have hlast : a (n - 1) ≤ a m := hanti (by omega)
    have hmmid : a m ≤ theta 0 := hmiddle m hm
    have htailSplit : (∑ k ∈ Ico 1 n, a k) =
        (∑ k ∈ Ico 1 (n - 1), a k) + a (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [sum_Ico_succ_top (by omega)]
    have htail : (∑ k ∈ Ico 1 n, a k) ≤
        2 * (∑ k ∈ Ico 1 n, theta k) + theta 0 := by
      calc
        (∑ k ∈ Ico 1 n, a k) =
            (∑ k ∈ Ico 1 (n - 1), a k) + a (n - 1) := htailSplit
        _ ≤ 2 * (∑ k ∈ Icc 1 (m - 1), a k) + a m := by linarith
        _ ≤ 2 * (∑ k ∈ Ico 1 n, theta k) + theta 0 := by
          nlinarith
    linarith
  · have hstrict : ∀ k, k ∈ Icc 1 (n / 2) → 2 * k < n := by
      intro k hk
      rw [mem_Icc] at hk
      have hle : 2 * (n / 2) ≤ n := by omega
      omega
    have htail0 := antitone_sum_Ico_one_le_two_sum_Icc_half a ha0 hanti n
    have hfirst : (∑ k ∈ Icc 1 (n / 2), a k) ≤
        ∑ k ∈ Icc 1 (n / 2), theta k :=
      sum_le_sum fun k hk => hcomp k hk (hstrict k hk)
    have hsub : (∑ k ∈ Icc 1 (n / 2), theta k) ≤
        ∑ k ∈ Ico 1 n, theta k := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [mem_Icc] at hk
        rw [mem_Ico]
        omega
      · intro k _ _
        exact htheta0 k
    have htail : (∑ k ∈ Ico 1 n, a k) ≤
        2 * ∑ k ∈ Ico 1 n, theta k :=
      htail0.trans <| mul_le_mul_of_nonneg_left (hfirst.trans hsub) (by norm_num)
    linarith [htheta0 0]

end OSSS
end StatMech
