/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Combinatorics.Enumerative.Stirling

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- Auxiliary identity: `S(n+1, j+1) = ∑_{m=0}^n C(n,m) * S(m,j)`.

Fixing the element `n+1`, the block containing it has `n - m` other elements
for some `m`, chosen in `C(n,m)` ways, while the remaining `m` elements are
partitioned into `j` blocks in `S(m,j)` ways. The proof is by induction on `n`,
using Pascal's rule and the Stirling recurrence. -/
private theorem stirlingSecond_succ_eq_sum_choose_mul (n j : ℕ) :
    (n + 1).stirlingSecond (j + 1)
      = ∑ m ∈ Finset.range (n + 1), n.choose m * m.stirlingSecond j := by
  induction n generalizing j with
  | zero =>
    show (1).stirlingSecond (j + 1)
      = ∑ m ∈ Finset.range 1, (0).choose m * m.stirlingSecond j
    rw [Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, one_mul]
    cases j with
    | zero => rfl
    | succ t =>
      rw [Nat.stirlingSecond_eq_zero_of_lt (show 1 < t.succ + 1 by omega)]
      rfl
  | succ n ih =>
    cases j with
    | zero =>
      show (n + 1 + 1).stirlingSecond (0 + 1)
        = ∑ m ∈ Finset.range (n + 1 + 1), (n + 1).choose m * m.stirlingSecond 0
      rw [Nat.stirlingSecond_one_right]
      symm
      trans (n + 1).choose 0 * Nat.stirlingSecond 0 0
      · apply Finset.sum_eq_single 0
        · intro m _ hm
          cases m with
          | zero => exact (hm rfl).elim
          | succ t => simp [Nat.stirlingSecond_succ_zero]
        · intro h
          simp [Finset.mem_range] at h
      · simp
    | succ t =>
      have ih1 := ih (t + 1)
      have ih2 := ih t
      have h0 : (n + 1).choose 0 * Nat.stirlingSecond 0 (t + 1) = 0 := by simp
      have pascal : ∀ m, (n + 1).choose (m + 1) = n.choose m + n.choose (m + 1) :=
        fun m => Nat.choose_succ_succ n m
      have stir : ∀ m, (m + 1).stirlingSecond (t + 1)
          = (t + 1) * m.stirlingSecond (t + 1) + m.stirlingSecond t :=
        fun m => Nat.stirlingSecond_succ_succ m t
      -- Shift identity: reindexing `k = m + 1`, both sides equal the sum over
      -- `Finset.range (n + 2)` (the dropped end terms vanish).
      have shift : ∑ m ∈ Finset.range (n + 1),
            n.choose (m + 1) * (m + 1).stirlingSecond (t + 1)
          = ∑ m ∈ Finset.range (n + 1), n.choose m * m.stirlingSecond (t + 1) := by
        have h1 : ∑ k ∈ Finset.range (n + 2), n.choose k * k.stirlingSecond (t + 1)
            = ∑ m ∈ Finset.range (n + 1),
              n.choose (m + 1) * (m + 1).stirlingSecond (t + 1) := by
          rw [Finset.sum_range_succ']
          simp
        have h2 : ∑ k ∈ Finset.range (n + 2), n.choose k * k.stirlingSecond (t + 1)
            = ∑ m ∈ Finset.range (n + 1), n.choose m * m.stirlingSecond (t + 1) := by
          rw [Finset.sum_range_succ]
          simp
        rw [← h1, h2]
      have sum_eq : ∑ m ∈ Finset.range (n + 1),
            (n + 1).choose (m + 1) * (m + 1).stirlingSecond (t + 1)
          = (t + 1) * (∑ m ∈ Finset.range (n + 1), n.choose m * m.stirlingSecond (t + 1))
            + (∑ m ∈ Finset.range (n + 1), n.choose m * m.stirlingSecond t)
            + ∑ m ∈ Finset.range (n + 1),
              n.choose (m + 1) * (m + 1).stirlingSecond (t + 1) := by
        trans ∑ m ∈ Finset.range (n + 1),
          ((t + 1) * (n.choose m * m.stirlingSecond (t + 1))
            + n.choose m * m.stirlingSecond t
            + n.choose (m + 1) * (m + 1).stirlingSecond (t + 1))
        · apply Finset.sum_congr rfl
          intro m _
          rw [pascal m, stir m]
          ring
        · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      have rhs_eq : ∑ m ∈ Finset.range (n + 1 + 1),
            (n + 1).choose m * m.stirlingSecond (t + 1)
          = ∑ m ∈ Finset.range (n + 1),
            (n + 1).choose (m + 1) * (m + 1).stirlingSecond (t + 1) := by
        rw [Finset.sum_range_succ', h0, add_zero]
      have lhs_eq : (n + 1 + 1).stirlingSecond (t + 1 + 1)
          = (t + 1 + 1) * (∑ m ∈ Finset.range (n + 1), n.choose m * m.stirlingSecond (t + 1))
            + ∑ m ∈ Finset.range (n + 1), n.choose m * m.stirlingSecond t := by
        rw [Nat.stirlingSecond_succ_succ, ih1, ih2]
      rw [lhs_eq, rhs_eq, sum_eq, shift]
      ring

/-- **Bell numbers are row sums of Stirling numbers of the second kind.** For every
natural number $n$, the Bell number $B_n$ equals $\sum_{k=0}^{n} S(n, k)$, where $S(n, k)$ is the
Stirling number of the second kind.

Source: Michael Z. Spivey, *A Generalized Recurrence for Bell Numbers*,
Journal of Integer Sequences 11 (2008), Article 08.2.5, equation `Stir`,
lines 107–108 (quoting the classical formula),
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Spivey/spivey25.tex>.
Proves `Wanted` entry `bell_eq_sum_stirlingSecond`.
-/
theorem bell_eq_sum_stirlingSecond (n : ℕ) : n.bell = ∑ k ∈ Finset.range (n + 1),
  n.stirlingSecond k := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic]
    have hsub : ∀ i ∈ Finset.range (n + 1),
        Finset.range (n - i + 1) ⊆ Finset.range (n + 1) := by
      intro i hi k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    have inner : ∀ k ∈ Finset.range (n + 1),
        (∑ i ∈ Finset.range (n + 1), n.choose i * (n - i).stirlingSecond k)
          = (n + 1).stirlingSecond (k + 1) := by
      intro k hk
      have hreflect : (∑ i ∈ Finset.range (n + 1), n.choose i * (n - i).stirlingSecond k)
          = ∑ j ∈ Finset.range (n + 1),
            n.choose (n + 1 - 1 - j) * (n - (n + 1 - 1 - j)).stirlingSecond k :=
        (Finset.sum_range_reflect _ _).symm
      rw [hreflect, stirlingSecond_succ_eq_sum_choose_mul n k]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < n + 1 := Finset.mem_range.mp hj
      have hjle : j ≤ n := by omega
      have e1 : n + 1 - 1 - j = n - j := by omega
      rw [e1, Nat.choose_symm hjle, Nat.sub_sub_self hjle]
    have hfin : (∑ k ∈ Finset.range (n + 1 + 1), (n + 1).stirlingSecond k)
        = ∑ k ∈ Finset.range (n + 1), (n + 1).stirlingSecond (k + 1) := by
      rw [Finset.sum_range_succ' (fun k => (n + 1).stirlingSecond k) (n + 1)]
      simp
    trans ∑ k ∈ Finset.range (n + 1), (n + 1).stirlingSecond (k + 1)
    · trans ∑ i ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1), n.choose i * (n - i).stirlingSecond k
      · apply Finset.sum_congr rfl
        intro i hi
        have hlt : n - i < n + 1 := Nat.lt_succ_of_le (Nat.sub_le n i)
        rw [ih (n - i) hlt, Finset.mul_sum]
        apply Finset.sum_subset (hsub i hi)
        intro k hk1 hk2
        simp only [Finset.mem_range, not_lt] at hk1 hk2
        have hlt : n - i < k := by omega
        rw [Nat.stirlingSecond_eq_zero_of_lt hlt, mul_zero]
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        exact inner k hk
    · exact hfin.symm

end

end MetaMathlibExt
