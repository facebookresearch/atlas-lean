/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Random.ExpectedCost
public import CSLibExt.Algorithms.Lean.Sort.Quick
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Harmonic.Defs

import all CSLibExt.Algorithms.Lean.Sort.QuickExpected
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Randomized quicksort: expected comparisons

The expected-comparison recurrence `E (n+1) = n + (2/(n+1)) *
sum_{k <= n} E k` has closed form `2 (n+2) H (n+1) - 4 (n+1)`,
hence `E n <= 2 n H n`, where `H` is Mathlib's `harmonic`. (An earlier
draft of the closed form, `2 (n+1) (H (n+1) - 1)`, was refuted at
`n = 1` during this work: `E 2 = 1`.) This is roadmap package ALG-10a
of the Atlas TCS canon roadmap.

The recurrence solution is the formal expectation of `QuickExpected`:
`quickSort_expectedTime_uniformPermutation_eq_qsExpected` shows that the
expected comparison count of `quickSort` on a uniformly random ordering of
a duplicate-free list of length `n` is `qsExpected n`, and
`quickSort_expectedTime_uniformPermutation_eq_harmonic` states it as
`2 (n+1) H n - 4 n`. The proof evaluates the pair sum `∑_{a<b} 2 / (d + 2)`
of `quickSort_expectedTime_uniformPermutation_toReal` by induction on the
set of input values, adding the largest value last.

Source: CLRS (4th ed.), Section 7.4.
-/

namespace Cslib.Algorithms.Lean.TimeM

/-- The randomized-quicksort expected-comparison recurrence:
`E 0 = 0` and `E (n + 1) = n + (2 / (n + 1)) * ∑_{k ≤ n} E k`
(the pivot is uniform, and after splitting, the two subproblems
have sizes `k` and `n - k`; summing the recurrence solution
against the pair-count identity gives the closed form below). -/
noncomputable def qsPair : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | (n + 1) =>
      let previous := qsPair n
      let e := (n : ℝ) + (2 / (n + 1 : ℝ)) * previous.2
      (e, previous.2 + e)

/-- Expected number of comparisons of randomized quicksort on
`n` distinct keys, defined through `qsPair` (whose second
component is the running sum `∑_{k ≤ n} qsExpected k`).
`quickSort_expectedTime_uniformPermutation_eq_qsExpected` identifies it
with the formal expectation of `quickSort` on a uniformly random ordering. -/
noncomputable def qsExpected (n : ℕ) : ℝ := (qsPair n).1

private theorem harmonic_succ_real (n : ℕ) :
    (harmonic (n + 1) : ℝ) = harmonic n + 1 / ((n : ℝ) + 1) := by
  rw [harmonic_succ]
  push_cast
  ring

private theorem harmonic_nonneg_real (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ_real]
    positivity

private theorem harmonic_le_real (n : ℕ) : (harmonic n : ℝ) ≤ (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ_real]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    push_cast
    linarith

private theorem qsPair_eq (n : ℕ) :
    qsPair n = (2 * ((n : ℝ) + 1) * harmonic n - 4 * (n : ℝ),
                ((n : ℝ) + 1) * ((n : ℝ) + 2) * harmonic (n + 1)
                  - ((n : ℝ) + 1) * (5 * (n : ℝ) + 4) / 2) := by
  induction n with
  | zero =>
    simp [qsPair]
    norm_num
  | succ n ih =>
    simp only [qsPair, ih]
    apply Prod.ext
    · simp only
      push_cast
      have h1 : ((n : ℝ) + 1) ≠ 0 := by
        have hk := Nat.cast_nonneg (α := ℝ) n
        linarith
      rw [harmonic_succ_real]
      field_simp
      ring
    · simp only
      push_cast
      have h1 : ((n : ℝ) + 1) ≠ 0 := by
        have hk := Nat.cast_nonneg (α := ℝ) n
        linarith
      have h2 : ((n : ℝ) + 2) ≠ 0 := by
        have hk := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hH : (harmonic (n + 1 + 1) : ℝ) = harmonic (n + 1) + 1 / ((n : ℝ) + 2) := by
        rw [harmonic_succ_real]
        push_cast
        ring
      rw [hH]
      field_simp
      ring

private theorem qsExpected_form (n : ℕ) :
    qsExpected n = 2 * ((n : ℝ) + 1) * harmonic n - 4 * (n : ℝ) := by
  simp [qsExpected, qsPair_eq]

/-- Expected comparisons of randomized quicksort are at most
`2 n H n`. -/
theorem qsExpected_le (n : ℕ) : qsExpected n ≤ 2 * n * (harmonic n : ℝ) := by
  cases n with
  | zero =>
    simp [qsExpected, qsPair]
  | succ n =>
    have h := qsExpected_form (n + 1)
    rw [h]
    push_cast
    have hHle : (harmonic (n + 1) : ℝ) ≤ ((n : ℝ) + 1) := by
      have hle := harmonic_le_real (n + 1)
      push_cast at hle
      exact hle
    have hHnonneg : 0 ≤ (harmonic (n + 1) : ℝ) := harmonic_nonneg_real _
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [hHle, hHnonneg, hnnonneg]

/-- The pair-count identity behind the bound: closed form
`qsExpected (n + 1) = 2 * (n + 2) * harmonic (n + 1) - 4 * (n + 1)`
(the exact expected number of comparisons is
`2 (n+2) H (n+1) - 4 (n+1)`, i.e. `2 (n+1) H n - 4 n`). -/
theorem qsExpected_eq (n : ℕ) :
    qsExpected (n + 1) = 2 * (n + 2) * (harmonic (n + 1) : ℝ) - 4 * (n + 1) := by
  have h := qsExpected_form (n + 1)
  rw [h]
  push_cast
  ring

section FormalExpectation

variable {α : Type*} [LinearOrder α]

/-- The pair sum `∑_{a < b} 2 / (d + 2)` over a finite set `S` of values,
where `d` counts the values of `S` strictly between `a` and `b`. -/
private noncomputable def valuePairSum (S : Finset α) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S,
    if a < b then (2 : ℝ) / ((S.filter (fun x => a < x ∧ x < b)).card + 2) else 0

/-- Over a finite set `T`, the counts `#{x ∈ T | a < x}` run through
`0, …, |T| - 1`. -/
private theorem sum_two_div_card_gt (T : Finset α) :
    ∑ a ∈ T, (2 : ℝ) / ((T.filter (fun x => a < x)).card + 2) =
      ∑ j ∈ Finset.range T.card, (2 : ℝ) / (j + 2) := by
  induction T using Finset.induction_on_min with
  | empty => simp
  | insert m U hm ih =>
    have hmU : m ∉ U := fun h => lt_irrefl m (hm m h)
    have hmin : (insert m U).filter (fun x => m < x) = U := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hx
      · exact fun hx => ⟨Or.inr hx, hm x hx⟩
    have hrest : ∑ a ∈ U, (2 : ℝ) / (((insert m U).filter (fun x => a < x)).card + 2) =
        ∑ a ∈ U, (2 : ℝ) / ((U.filter (fun x => a < x)).card + 2) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.filter_insert, ite_eq_right (not_lt.mpr (hm a ha).le)]
    rw [Finset.sum_insert hmU, hmin, hrest, ih, Finset.card_insert_of_notMem hmU,
      Finset.sum_range_succ, add_comm]

/-- Adding a value `m` above every value of `T` adds the pairs `(a, m)`
for `a ∈ T`; the values strictly between `a` and `m` are those of `T`
above `a`. -/
private theorem valuePairSum_insert_max {m : α} {T : Finset α} (hm : ∀ x ∈ T, x < m) :
    valuePairSum (insert m T) =
      valuePairSum T + ∑ a ∈ T, (2 : ℝ) / ((T.filter (fun x => a < x)).card + 2) := by
  have hmT : m ∉ T := fun h => lt_irrefl m (hm m h)
  have hfirst : (∑ b ∈ insert m T, if m < b then
      (2 : ℝ) / (((insert m T).filter (fun x => m < x ∧ x < b)).card + 2) else 0) = 0 := by
    refine Finset.sum_eq_zero fun b hb => ite_eq_right fun hmb => ?_
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact lt_irrefl _ hmb
    · exact lt_asymm hmb (hm b hb)
  have hrow : ∀ a ∈ T,
      (∑ b ∈ insert m T, if a < b then
          (2 : ℝ) / (((insert m T).filter (fun x => a < x ∧ x < b)).card + 2) else 0) =
        (∑ b ∈ T, if a < b then
          (2 : ℝ) / ((T.filter (fun x => a < x ∧ x < b)).card + 2) else 0) +
        (2 : ℝ) / ((T.filter (fun x => a < x)).card + 2) := by
    intro a ha
    have htop : (insert m T).filter (fun x => a < x ∧ x < m) = T.filter (fun x => a < x) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hax, hxm⟩
        · exact absurd hxm (lt_irrefl _)
        · exact ⟨hx, hax⟩
      · rintro ⟨hx, hax⟩
        exact ⟨Or.inr hx, hax, hm x hx⟩
    have hinner : ∀ b ∈ T, (insert m T).filter (fun x => a < x ∧ x < b) =
        T.filter (fun x => a < x ∧ x < b) := by
      intro b hb
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hax, hxb⟩
        · exact absurd (hxb.trans (hm b hb)) (lt_irrefl _)
        · exact ⟨hx, hax, hxb⟩
      · rintro ⟨hx, hax, hxb⟩
        exact ⟨Or.inr hx, hax, hxb⟩
    rw [Finset.sum_insert hmT, ite_eq_left (hm a ha), htop, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun b hb => by rw [hinner b hb]
  unfold valuePairSum
  rw [Finset.sum_insert hmT, hfirst, zero_add, Finset.sum_congr rfl hrow,
    Finset.sum_add_distrib]

private theorem sum_range_two_div (k : ℕ) :
    ∑ j ∈ Finset.range k, (2 : ℝ) / (j + 2) = 2 * harmonic (k + 1) - 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ_real (k + 1)]
    push_cast
    ring

/-- The pair sum over a set of `n` values is `2 (n + 1) H n - 4 n`. -/
private theorem valuePairSum_eq (S : Finset α) :
    valuePairSum S = 2 * ((S.card : ℝ) + 1) * harmonic S.card - 4 * S.card := by
  induction S using Finset.induction_on_max with
  | empty => simp [valuePairSum]
  | insert m T hm ih =>
    have hmT : m ∉ T := fun h => lt_irrefl m (hm m h)
    have hk : ((T.card : ℝ) + 1) ≠ 0 := by positivity
    rw [valuePairSum_insert_max hm, ih, sum_two_div_card_gt, sum_range_two_div,
      Finset.card_insert_of_notMem hmT, harmonic_succ_real]
    push_cast
    field_simp
    ring

private theorem betweenCount_eq_card_toFinset {xs : List α} (hxs : xs.Nodup) (a b : α) :
    betweenCount xs a b = (xs.toFinset.filter (fun x => a < x ∧ x < b)).card := by
  rw [List.filter_toFinset, List.toFinset_card_of_nodup (hxs.filter _)]
  rfl

/-- The expected number of comparisons of `quickSort` on a uniformly random
ordering of a duplicate-free list of length `n` is exactly
`2 (n + 1) H n - 4 n` (CLRS Section 7.4). This sharpens the upper bound
`quickSort_expectedTime_le_harmonic`. -/
theorem quickSort_expectedTime_uniformPermutation_eq_harmonic (xs : List α)
    (hxs : xs.Nodup) :
    (expectedTime quickSort (uniformPermutation xs)).toReal =
      2 * ((xs.length : ℝ) + 1) * harmonic xs.length - 4 * xs.length := by
  have hsum : (expectedTime quickSort (uniformPermutation xs)).toReal =
      valuePairSum xs.toFinset := by
    rw [quickSort_expectedTime_uniformPermutation_toReal xs hxs, Finset.sum_filter,
      Finset.sum_product]
    unfold valuePairSum
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [betweenCount_eq_card_toFinset hxs]
  rw [hsum, valuePairSum_eq, List.toFinset_card_of_nodup hxs]

/-- The formal expected comparison count of `quickSort` on a uniformly
random ordering of a duplicate-free list is `qsExpected` of its length. -/
theorem quickSort_expectedTime_uniformPermutation_eq_qsExpected (xs : List α)
    (hxs : xs.Nodup) :
    (expectedTime quickSort (uniformPermutation xs)).toReal = qsExpected xs.length := by
  rw [quickSort_expectedTime_uniformPermutation_eq_harmonic xs hxs, qsExpected_form]

end FormalExpectation

end Cslib.Algorithms.Lean.TimeM
