/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Basic
import Mathlib.Tactic.Ring

/-!
# Longest increasing subsequence: the quadratic dynamic program

CLRS, third edition, Exercise 15.4-5 asks for an `O(n²)` algorithm that finds a longest
monotonically increasing subsequence of a sequence of `n` numbers. A subsequence is
`List.Sublist` (`<+`), not necessarily contiguous; increasing is read strictly, as
`List.Pairwise (· < ·)`.

The dynamic program computes, for every position `i`, a longest strictly increasing subsequence
that starts at position `i`: its length is `L i = 1 + max {L j | i < j, xs[i] < xs[j]}` (the
maximum of the empty set is `0`), and the subsequence itself is `xs[i]` followed by the stored
subsequence of a maximizing `j`. This is the suffix form of the textbook recurrence; reading the
list right to left gives the "ends at `i`" form. `lisTable` builds the table of triples
`(xs[i], L i, tail)` from the right, scanning the already-built table once for each new element,
and `longestIncreasingSubsequence` returns the stored subsequence of a largest entry.

Correctness: the result is a strictly increasing subsequence of `xs`
(`longestIncreasingSubsequence_sublist`, `longestIncreasingSubsequence_pairwise`) at least as long
as every strictly increasing subsequence (`length_le_longestIncreasingSubsequence`); equivalently
its length is the optimum (`length_longestIncreasingSubsequence_eq_iff`). The empty list gives
`[]`. Values come from any preorder with decidable `<` in `Type`; the table pairs values with
lengths inside one `TimeM ℕ` computation, which fixes the universe.

## Cost model

One unit for each table entry inspected: adding element `i` scans the `n - 1 - i` entries to its
right, comparing `xs[i] < xs[j]` and the cached lengths, and the final pass inspects each of the
`n` entries once. Arithmetic on lengths, list construction and recursion are free; the stored
subsequence of a new entry is one cons onto a stored subsequence, shared rather than copied. The
total is exactly `n * (n + 1) / 2`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open scoped List

variable {α : Type} [Preorder α] [DecidableLT α]

omit [DecidableLT α] in
/-- `k` is the length of a longest strictly increasing subsequence of `xs`. -/
def IsLISLength (xs : List α) (k : ℕ) : Prop :=
  (∃ ys, ys <+ xs ∧ ys.Pairwise (· < ·) ∧ ys.length = k) ∧
    ∀ ys, ys <+ xs → ys.Pairwise (· < ·) → ys.length ≤ k

omit [DecidableLT α] in
/-- The table cell for the occurrence of `x` followed by the suffix `s`: `x :: zs` is a longest
strictly increasing subsequence of `x :: s` that starts with this `x`, and `k` is its length. -/
def IsLISCell (x : α) (s : List α) (k : ℕ) (zs : List α) : Prop :=
  zs <+ s ∧ (x :: zs).Pairwise (· < ·) ∧ zs.length + 1 = k ∧
    ∀ zs', zs' <+ s → (x :: zs').Pairwise (· < ·) → zs'.length + 1 ≤ k

/-- Among table entries `(y, k, zs)` with `x < y`, one with the largest `k`, returned as
`(k, y :: zs)`, or `(0, [])` if there is none; one unit per entry. -/
def maxAbove (x : α) : List (α × ℕ × List α) → TimeM ℕ (ℕ × List α)
  | [] => pure (0, [])
  | (y, k, zs) :: t => do
      ✓
      let b ← maxAbove x t
      pure (if x < y ∧ b.1 < k then (k, y :: zs) else b)

/-- The table `(xs[i], L i, tail)` for every position `i`, built from the right. -/
def lisTable : List α → TimeM ℕ (List (α × ℕ × List α))
  | [] => pure []
  | x :: rest => do
      let t ← lisTable rest
      let b ← maxAbove x t
      pure ((x, b.1 + 1, b.2) :: t)

omit [Preorder α] [DecidableLT α] in
/-- A table entry with the largest length, returned as `(k, y :: zs)`, or `(0, [])` for the
empty table; one unit per entry. -/
def maxEntry : List (α × ℕ × List α) → TimeM ℕ (ℕ × List α)
  | [] => pure (0, [])
  | (y, k, zs) :: t => do
      ✓
      let b ← maxEntry t
      pure (if b.1 < k then (k, y :: zs) else b)

/-- A longest strictly increasing subsequence, by the quadratic dynamic program. -/
def longestIncreasingSubsequence (xs : List α) : TimeM ℕ (List α) := do
  let t ← lisTable xs
  let b ← maxEntry t
  pure b.2

/-! ## Cost -/

@[simp]
theorem maxAbove_time (x : α) (t : List (α × ℕ × List α)) :
    (maxAbove x t).time = t.length := by
  induction t with
  | nil => simp [maxAbove]
  | cons e t ih =>
      obtain ⟨y, k, zs⟩ := e
      simp [maxAbove, ih, Nat.add_comm]

omit [Preorder α] [DecidableLT α] in
@[simp]
theorem maxEntry_time (t : List (α × ℕ × List α)) : (maxEntry t).time = t.length := by
  induction t with
  | nil => simp [maxEntry]
  | cons e t ih =>
      obtain ⟨y, k, zs⟩ := e
      simp [maxEntry, ih, Nat.add_comm]

@[simp]
theorem lisTable_length (xs : List α) : (lisTable xs).ret.length = xs.length := by
  induction xs with
  | nil => simp [lisTable]
  | cons x xs ih => simp [lisTable, ih]

theorem lisTable_time (xs : List α) : 2 * (lisTable xs).time = xs.length * (xs.length - 1) := by
  induction xs with
  | nil => simp [lisTable]
  | cons x xs ih =>
      simp only [lisTable, time_bind, maxAbove_time, lisTable_length, time_pure,
        List.length_cons, Nat.add_sub_cancel, Nat.add_zero]
      obtain ⟨n, hn⟩ : ∃ n, xs.length = n := ⟨_, rfl⟩
      rw [hn] at ih ⊢
      rcases n with _ | n
      · simp only [Nat.zero_mul] at ih
        omega
      · simp only [Nat.add_sub_cancel] at ih
        rw [Nat.mul_add, ih]
        ring

/-- The dynamic program inspects exactly `n * (n + 1) / 2` table entries. -/
theorem longestIncreasingSubsequence_time (xs : List α) :
    2 * (longestIncreasingSubsequence xs).time = xs.length * (xs.length + 1) := by
  simp only [longestIncreasingSubsequence, time_bind, maxEntry_time, lisTable_length, time_pure,
    Nat.add_zero, Nat.mul_add, lisTable_time]
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n := ⟨_, rfl⟩
  rw [hn]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    ring

/-! ## Correctness -/

omit [Preorder α] [DecidableLT α] in
/-- A subsequence starting with `y` starts at some occurrence of `y`: it is `y` followed by a
subsequence of the suffix after that occurrence. -/
theorem exists_suffix_of_cons_sublist {y : α} {zs l : List α} (h : y :: zs <+ l) :
    ∃ s, y :: s <:+ l ∧ zs <+ s := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons a l ih =>
      rcases List.sublist_cons_iff.1 h with h | ⟨r, hr, hzs⟩
      · obtain ⟨s, hs, hzs⟩ := ih h
        exact ⟨s, hs.trans (List.suffix_cons _ _), hzs⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hr
        exact ⟨l, List.suffix_refl _, hzs⟩

omit [DecidableLT α] in
/-- The table invariant: every entry is the cell of some occurrence, and every occurrence has a
cell in the table. -/
def LISTableSpec (l : List α) (t : List (α × ℕ × List α)) : Prop :=
  (∀ y k zs, (y, k, zs) ∈ t → ∃ s, y :: s <:+ l ∧ IsLISCell y s k zs) ∧
    ∀ y s, y :: s <:+ l → ∃ k zs, (y, k, zs) ∈ t ∧ IsLISCell y s k zs

theorem maxAbove_spec (x : α) (t : List (α × ℕ × List α)) :
    (∀ y k zs, (y, k, zs) ∈ t → x < y → k ≤ (maxAbove x t).ret.1) ∧
      ((maxAbove x t).ret = (0, []) ∨
        ∃ y zs, (y, (maxAbove x t).ret.1, zs) ∈ t ∧ x < y ∧ (maxAbove x t).ret.2 = y :: zs) := by
  induction t with
  | nil => simp [maxAbove]
  | cons e t ih =>
      obtain ⟨y, k, zs⟩ := e
      obtain ⟨hle, hatt⟩ := ih
      simp only [maxAbove, ret_bind, ret_pure]
      set b := (maxAbove x t).ret
      by_cases hc : x < y ∧ b.1 < k
      · simp only [hc, and_self, ite_true]
        refine ⟨fun y' k' zs' hmem hx => ?_, Or.inr ⟨y, zs, List.mem_cons_self, hc.1, rfl⟩⟩
        rcases List.mem_cons.1 hmem with h | h
        · obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
          exact le_rfl
        · exact (hle y' k' zs' h hx).trans hc.2.le
      · simp only [hc, ite_false]
        refine ⟨fun y' k' zs' hmem hx => ?_, ?_⟩
        · rcases List.mem_cons.1 hmem with h | h
          · obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
            exact Nat.le_of_not_lt (fun hlt => hc ⟨hx, hlt⟩)
          · exact hle y' k' zs' h hx
        · rcases hatt with h0 | ⟨y', zs', hy', hx, hw⟩
          · exact Or.inl h0
          · exact Or.inr ⟨y', zs', List.mem_cons_of_mem _ hy', hx, hw⟩

/-- The recurrence: if the table for `rest` is correct, the entry built for the new head `x` is
its cell. -/
theorem isLISCell_maxAbove {x : α} {rest : List α} {t : List (α × ℕ × List α)}
    (ht : LISTableSpec rest t) :
    IsLISCell x rest ((maxAbove x t).ret.1 + 1) (maxAbove x t).ret.2 := by
  obtain ⟨hle, hatt⟩ := maxAbove_spec x t
  refine ⟨?_, ?_, ?_, fun zs hzs hpair => ?_⟩
  · rcases hatt with h0 | ⟨y, zs, hy, -, hw⟩
    · simp [h0]
    · obtain ⟨s, hs, hzs, -, -, -⟩ := ht.1 y _ zs hy
      rw [hw]
      exact (List.cons_sublist_cons.2 hzs).trans hs.sublist
  · rcases hatt with h0 | ⟨y, zs, hy, hxy, hw⟩
    · simp [h0]
    · obtain ⟨s, -, -, hpair, -, -⟩ := ht.1 y _ zs hy
      rw [hw]
      refine List.Pairwise.cons (fun z hz => ?_) hpair
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy
      · exact hxy.trans (List.rel_of_pairwise_cons hpair hz)
  · rcases hatt with h0 | ⟨y, zs, hy, -, hw⟩
    · simp [h0]
    · obtain ⟨s, -, -, -, hlen, -⟩ := ht.1 y _ zs hy
      rw [hw, List.length_cons, hlen]
  · match zs, hzs, hpair with
    | [], _, _ => simp
    | y :: zs', hzs, hpair =>
        have hxy : x < y := List.rel_of_pairwise_cons hpair List.mem_cons_self
        obtain ⟨s, hs, hzs'⟩ := exists_suffix_of_cons_sublist hzs
        obtain ⟨k, w, hk, -, -, -, hkle⟩ := ht.2 y s hs
        have := hkle zs' hzs' (List.Pairwise.of_cons hpair)
        have := hle y k w hk hxy
        simp only [List.length_cons]
        omega

theorem lisTable_spec (xs : List α) : LISTableSpec xs (lisTable xs).ret := by
  induction xs with
  | nil =>
      refine ⟨by simp [lisTable], fun y s h => ?_⟩
      exact absurd (List.eq_nil_of_suffix_nil h) (by simp)
  | cons x rest ih =>
      simp only [lisTable, ret_bind, ret_pure]
      have hx := isLISCell_maxAbove (x := x) ih
      refine ⟨fun y k zs hmem => ?_, fun y s hs => ?_⟩
      · rcases List.mem_cons.1 hmem with h | h
        · obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
          exact ⟨rest, List.suffix_refl _, hx⟩
        · obtain ⟨s, hs, hk⟩ := ih.1 y k zs h
          exact ⟨s, hs.trans (List.suffix_cons _ _), hk⟩
      · rcases List.suffix_cons_iff.1 hs with h | h
        · obtain ⟨rfl, rfl⟩ := List.cons.inj h
          exact ⟨_, _, List.mem_cons_self, hx⟩
        · obtain ⟨k, zs, hk, hks⟩ := ih.2 y s h
          exact ⟨k, zs, List.mem_cons_of_mem _ hk, hks⟩

omit [Preorder α] [DecidableLT α] in
theorem maxEntry_spec (t : List (α × ℕ × List α)) :
    (∀ y k zs, (y, k, zs) ∈ t → k ≤ (maxEntry t).ret.1) ∧
      ((maxEntry t).ret = (0, []) ∨
        ∃ y zs, (y, (maxEntry t).ret.1, zs) ∈ t ∧ (maxEntry t).ret.2 = y :: zs) := by
  induction t with
  | nil => simp [maxEntry]
  | cons e t ih =>
      obtain ⟨y, k, zs⟩ := e
      obtain ⟨hle, hatt⟩ := ih
      simp only [maxEntry, ret_bind, ret_pure]
      set b := (maxEntry t).ret
      by_cases hc : b.1 < k
      · simp only [hc, ite_true]
        refine ⟨fun y' k' zs' hmem => ?_, Or.inr ⟨y, zs, List.mem_cons_self, rfl⟩⟩
        rcases List.mem_cons.1 hmem with h | h
        · obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
          exact le_rfl
        · exact (hle y' k' zs' h).trans hc.le
      · simp only [hc, ite_false]
        refine ⟨fun y' k' zs' hmem => ?_, ?_⟩
        · rcases List.mem_cons.1 hmem with h | h
          · obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
            exact Nat.le_of_not_lt hc
          · exact hle y' k' zs' h
        · rcases hatt with h0 | ⟨y', zs', hy', hw⟩
          · exact Or.inl h0
          · exact Or.inr ⟨y', zs', List.mem_cons_of_mem _ hy', hw⟩

/-- The returned list is a strictly increasing subsequence of maximum length. -/
theorem longestIncreasingSubsequence_spec (xs : List α) :
    (longestIncreasingSubsequence xs).ret <+ xs ∧
      (longestIncreasingSubsequence xs).ret.Pairwise (· < ·) ∧
      ∀ ys, ys <+ xs → ys.Pairwise (· < ·) →
        ys.length ≤ (longestIncreasingSubsequence xs).ret.length := by
  have ht := lisTable_spec xs
  obtain ⟨hle, hatt⟩ := maxEntry_spec (lisTable xs).ret
  simp only [longestIncreasingSubsequence, ret_bind, ret_pure]
  set b := (maxEntry (lisTable xs).ret).ret
  have hlen : b.2.length = b.1 := by
    rcases hatt with h0 | ⟨y, zs, hy, hw⟩
    · simp [h0]
    · obtain ⟨s, -, -, -, hzlen, -⟩ := ht.1 y _ zs hy
      rw [hw, List.length_cons, hzlen]
  refine ⟨?_, ?_, fun ys hys hpair => ?_⟩
  · rcases hatt with h0 | ⟨y, zs, hy, hw⟩
    · simp [h0]
    · obtain ⟨s, hs, hzs, -, -, -⟩ := ht.1 y _ zs hy
      rw [hw]
      exact (List.cons_sublist_cons.2 hzs).trans hs.sublist
  · rcases hatt with h0 | ⟨y, zs, hy, hw⟩
    · simp [h0]
    · obtain ⟨s, -, -, hpair, -, -⟩ := ht.1 y _ zs hy
      rw [hw]
      exact hpair
  · rw [hlen]
    match ys, hys, hpair with
    | [], _, _ => simp
    | y :: zs, hys, hpair =>
        obtain ⟨s, hs, hzs⟩ := exists_suffix_of_cons_sublist hys
        obtain ⟨k, w, hk, -, -, -, hkle⟩ := ht.2 y s hs
        exact (hkle zs hzs hpair).trans (hle y k w hk)

theorem longestIncreasingSubsequence_sublist (xs : List α) :
    (longestIncreasingSubsequence xs).ret <+ xs :=
  (longestIncreasingSubsequence_spec xs).1

theorem longestIncreasingSubsequence_pairwise (xs : List α) :
    (longestIncreasingSubsequence xs).ret.Pairwise (· < ·) :=
  (longestIncreasingSubsequence_spec xs).2.1

theorem length_le_longestIncreasingSubsequence {xs ys : List α} (hys : ys <+ xs)
    (hpair : ys.Pairwise (· < ·)) : ys.length ≤ (longestIncreasingSubsequence xs).ret.length :=
  (longestIncreasingSubsequence_spec xs).2.2 ys hys hpair

/-- The length of the returned subsequence is the optimum. -/
theorem isLISLength_longestIncreasingSubsequence (xs : List α) :
    IsLISLength xs (longestIncreasingSubsequence xs).ret.length :=
  ⟨⟨_, longestIncreasingSubsequence_sublist xs, longestIncreasingSubsequence_pairwise xs, rfl⟩,
    fun _ hys hpair => length_le_longestIncreasingSubsequence hys hpair⟩

omit [DecidableLT α] in
/-- The longest increasing subsequence length is unique. -/
theorem IsLISLength.unique {xs : List α} {k k' : ℕ} (h : IsLISLength xs k)
    (h' : IsLISLength xs k') : k = k' := by
  obtain ⟨ys, hys, hpair, rfl⟩ := h.1
  obtain ⟨ys', hys', hpair', rfl⟩ := h'.1
  exact le_antisymm (h'.2 ys hys hpair) (h.2 ys' hys' hpair')

/-- The returned subsequence has length `k` exactly when `k` is the optimum. -/
theorem length_longestIncreasingSubsequence_eq_iff (xs : List α) (k : ℕ) :
    (longestIncreasingSubsequence xs).ret.length = k ↔ IsLISLength xs k :=
  ⟨fun h => h ▸ isLISLength_longestIncreasingSubsequence xs,
    fun h => (isLISLength_longestIncreasingSubsequence xs).unique h⟩

end Cslib.Algorithms.Lean.TimeM
