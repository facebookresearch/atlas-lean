/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Fin

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

/-! # The median interval minimizes sample absolute deviation -/

open Finset

namespace MetaMathlibExt

private theorem pairLoss_eq {a b t : ℝ} (ha : a ≤ t) (hb : t ≤ b) :
    |a - t| + |b - t| = b - a := by
  rw [abs_of_nonpos (sub_nonpos.mpr ha), abs_of_nonneg (sub_nonneg.mpr hb)]
  linarith

private theorem pairLoss_le (a b t : ℝ) :
    b - a ≤ |a - t| + |b - t| := by
  linarith [neg_le_abs (a - t), le_abs_self (b - t)]

private theorem pairLoss_lt {a b t : ℝ} (hab : a ≤ b) (ht : t < a ∨ b < t) :
    b - a < |a - t| + |b - t| := by
  rcases ht with ht | ht
  · rw [abs_of_nonneg (sub_nonneg.mpr ht.le),
      abs_of_nonneg (sub_nonneg.mpr (ht.le.trans hab))]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (hab.trans ht.le)), abs_of_nonpos (sub_nonpos.mpr ht.le)]
    linarith

@[expose] public section

/-- **Absolute-deviation minimizers of a sample are the median interval.** For a nonempty
sample of `n + 1` real numbers, write its order statistics as a monotone sequence indexed by
`Fin (n + 1)`, counting repeated observations with their multiplicities. The minimizers of the
sum of absolute deviations are exactly the closed interval between the order statistics at
zero-based indices `n / 2` and its reverse `n - n / 2`. The interval collapses to a point for
an odd sample size or if the two middle order statistics agree. For an empty sample the sum
is identically zero and every real number minimizes it. -/
theorem sample_median_interval_iff_minimizes {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : Monotone x)
    (m : ℝ) :
    let a : Fin (n + 1) := ⟨n / 2, by omega⟩
    (∀ t : ℝ, (∑ i, |x i - m|) ≤ ∑ i, |x i - t|) ↔ x a ≤ m ∧ m ≤ x a.rev := by
  intro a
  let loss (t : ℝ) : ℝ := ∑ i, |x i - t|
  let pair (t : ℝ) (i : Fin (n + 1)) : ℝ := |x i - t| + |x i.rev - t|
  have ha_le : a ≤ a.rev := by
    change n / 2 ≤ a.rev.val
    rw [Fin.val_rev]
    change n / 2 ≤ n + 1 - (n / 2 + 1)
    omega
  have hnext (i : Fin (n + 1)) (hi : ¬ i ≤ a) : a.rev ≤ i := by
    have hi' : n / 2 < i.val := lt_of_not_ge hi
    change a.rev.val ≤ i.val
    rw [Fin.val_rev]
    change n + 1 - (n / 2 + 1) ≤ i.val
    omega
  have hsum (t : ℝ) : (∑ i, pair t i) = loss t + loss t := by
    dsimp only [pair, loss]
    rw [sum_add_distrib, Fin.rev_bijective.sum_comp (fun i => |x i - t|)]
  have hpair {s : ℝ} (hlo : x a ≤ s) (hhi : s ≤ x a.rev) (t : ℝ) (i : Fin (n + 1)) :
      pair s i ≤ pair t i := by
    by_cases hi : i ≤ a
    · have hr : a.rev ≤ i.rev := Fin.rev_le_rev.mpr hi
      change |x i - s| + |x i.rev - s| ≤ |x i - t| + |x i.rev - t|
      rw [pairLoss_eq ((hx hi).trans hlo) (hhi.trans (hx hr))]
      exact pairLoss_le _ _ _
    · have hj := hnext i hi
      have hr : i.rev ≤ a := by simpa only [Fin.rev_rev] using (Fin.rev_le_rev.mpr hj)
      change |x i - s| + |x i.rev - s| ≤ |x i - t| + |x i.rev - t|
      rw [add_comm |x i - s|, pairLoss_eq ((hx hr).trans hlo) (hhi.trans (hx hj)),
        add_comm |x i - t|]
      exact pairLoss_le _ _ _
  change (∀ t : ℝ, loss m ≤ loss t) ↔ x a ≤ m ∧ m ≤ x a.rev
  constructor
  · intro hmin
    by_contra h
    have hout : m < x a ∨ x a.rev < m := by
      rcases not_and_or.mp h with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (lt_of_not_ge h)
    have hstrict : pair (x a) a < pair m a := by
      change |x a - x a| + |x a.rev - x a| < |x a - m| + |x a.rev - m|
      rw [pairLoss_eq le_rfl (hx ha_le)]
      exact pairLoss_lt (hx ha_le) hout
    have htotal := sum_lt_sum (s := univ) (fun i _ => hpair le_rfl (hx ha_le) m i)
      ⟨a, mem_univ _, hstrict⟩
    rw [hsum, hsum] at htotal
    linarith [hmin (x a)]
  · rintro ⟨hlo, hhi⟩ t
    have htotal := sum_le_sum (s := univ) (fun i _ => hpair hlo hhi t i)
    rw [hsum, hsum] at htotal
    linarith

end

end MetaMathlibExt
