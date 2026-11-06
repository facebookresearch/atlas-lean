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
/-- **Length of a longest increasing subsequence.** For a list $xs$ over a preorder and a natural
number $k$, $k$ is the length of a longest strictly increasing subsequence of $xs$ when some
strictly increasing subsequence of $xs$ has length $k$ and every strictly increasing subsequence
of $xs$ has length at most $k$. Here a subsequence need not be contiguous, and strictly increasing
means that each element is strictly less than every later one. -/
def IsLISLength (xs : List α) (k : ℕ) : Prop :=
  (∃ ys, ys <+ xs ∧ ys.Pairwise (· < ·) ∧ ys.length = k) ∧
    ∀ ys, ys <+ xs → ys.Pairwise (· < ·) → ys.length ≤ k

omit [DecidableLT α] in
/-- **Table cell of the LIS dynamic program.** For an element $x$, lists $s$ and $zs$, and a
natural number $k$, the pair $(k, zs)$ is a table cell for $x$ followed by $s$ when $zs$ is a
subsequence (not necessarily contiguous) of $s$, the list $x$ followed by $zs$ is strictly
increasing (each element strictly less than every later one) and has length $k$, and for every
subsequence $zs'$ of $s$ such that $x$ followed by $zs'$ is strictly increasing, the list $x$
followed by $zs'$ has length at most $k$. So $x$ followed by $zs$ is a longest strictly increasing
subsequence of $x$ followed by $s$ that starts with this $x$. -/
def IsLISCell (x : α) (s : List α) (k : ℕ) (zs : List α) : Prop :=
  zs <+ s ∧ (x :: zs).Pairwise (· < ·) ∧ zs.length + 1 = k ∧
    ∀ zs', zs' <+ s → (x :: zs').Pairwise (· < ·) → zs'.length + 1 ≤ k

/-- **Best table entry above a value.** Given a value $x$ and a list $t$ of entries $(y, k, zs)$,
where $y$ is a value, $k$ a natural number and $zs$ a list of values, this timed computation
returns the pair of $k$ and the list $y$ followed by $zs$ for an entry of $t$ with $x < y$ whose
$k$ is largest among such entries, provided that $k$ is positive; if no entry with $x < y$ has
$k > 0$, it returns $0$ and the empty list. It costs one unit per entry of $t$. -/
def maxAbove (x : α) : List (α × ℕ × List α) → TimeM ℕ (ℕ × List α)
  | [] => pure (0, [])
  | (y, k, zs) :: t => do
      ✓
      let b ← maxAbove x t
      pure (if x < y ∧ b.1 < k then (k, y :: zs) else b)

/-- **Table of the quadratic LIS program.** The table of a list is a list of triples $(y, k, zs)$,
built from the right: the empty list has the empty table, and the table of $x$ followed by $rest$
is the table $t$ of $rest$ with the entry $(x, b + 1, w)$ put in front, where $(b, w)$ is the
result of the scan of $t$ for entries above $x$. Building the table costs the total cost of these
scans. -/
def lisTable : List α → TimeM ℕ (List (α × ℕ × List α))
  | [] => pure []
  | x :: rest => do
      let t ← lisTable rest
      let b ← maxAbove x t
      pure ((x, b.1 + 1, b.2) :: t)

omit [Preorder α] [DecidableLT α] in
/-- **Table entry of largest length.** Given a list $t$ of entries $(y, k, zs)$, where $k$ is a
natural number and $zs$ is a list with elements of the same type as $y$, this timed computation
returns the pair of $k$ and the list $y$ followed by $zs$ for an entry of $t$ whose $k$ is
largest, provided that this $k$ is positive, and returns $0$ and the empty list otherwise (in
particular when $t$ is empty). It costs one unit per entry of $t$. -/
def maxEntry : List (α × ℕ × List α) → TimeM ℕ (ℕ × List α)
  | [] => pure (0, [])
  | (y, k, zs) :: t => do
      ✓
      let b ← maxEntry t
      pure (if b.1 < k then (k, y :: zs) else b)

/-- **Longest increasing subsequence by dynamic programming.** Given a list
$x_0, \dots, x_{n-1}$ of elements of a preorder with decidable $<$, this timed computation
builds, from the right, a table recording for each position $i$ a length and a strictly
increasing subsequence starting with $x_i$ (the longest one, by the recurrence
$L_i = 1 + \max \{ L_j : i < j,\ x_i < x_j \}$ with $\max \emptyset = 0$), and returns the
stored subsequence of an entry of largest length, or the empty list when $n = 0$. The cost
is one unit for each table entry inspected: building the entry for position $i$ scans the
entries to its right, and the final scan inspects each entry once. -/
def longestIncreasingSubsequence (xs : List α) : TimeM ℕ (List α) := do
  let t ← lisTable xs
  let b ← maxEntry t
  pure b.2

/-! ## Cost -/

/-- **Cost of the scan for the best entry above a value.** Let $\alpha$ be a preorder with
decidable $<$. For every value $x \in \alpha$ and every list $t$ of entries $(y, k, zs)$, where
$y \in \alpha$, $k$ is a natural number and $zs$ is a list over $\alpha$, the scan of $t$ for the
best table entry above $x$ costs exactly the length of $t$. -/
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

/-- **Running time of the quadratic LIS program.** For every list $xs$ of length $n$ over a
preorder, twice the cost of the quadratic longest-increasing-subsequence program on $xs$ equals
$n(n + 1)$, so the program costs exactly $n(n + 1)/2$.

The cost model charges one unit for each table entry inspected. -/
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
/-- **A subsequence starting with $y$ starts at an occurrence of $y$.** For an element $y$ and lists
$zs$ and $l$, if the list $y$ followed by $zs$ is a subsequence (not necessarily contiguous) of $l$,
then there is a list $s$ such that $y$ followed by $s$ is a suffix of $l$ and $zs$ is a subsequence
of $s$. -/
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
/-- **Invariant of the LIS table.** A table $t$ of triples $(y, k, zs)$ satisfies the invariant for
a list $l$ when every entry $(y, k, zs)$ of $t$ has a list $s$ such that $y$ followed by $s$ is a
suffix of $l$ and $(k, zs)$ is a table cell for $y$ followed by $s$, and conversely, for every
element $y$ and list $s$ such that $y$ followed by $s$ is a suffix of $l$, some entry $(y, k, zs)$
of $t$ makes $(k, zs)$ a table cell for $y$ followed by $s$. -/
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

/-- **The step of the LIS recurrence.** Let $x$ be an element, $rest$ a list, and $t$ a table of
triples $(y, k, zs)$ that satisfies the invariant of the LIS table for $rest$. Let $(b, w)$ be the
result of the scan of $t$ for entries above $x$. Then $(b + 1, w)$ is a table cell for $x$ followed
by $rest$: $w$ is a subsequence of $rest$, the list $x$ followed by $w$ is strictly increasing and
has length $b + 1$, and every strictly increasing list $x$ followed by a subsequence of $rest$ has
length at most $b + 1$. -/
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

/-- **Correctness of the quadratic LIS program.** For every list $xs$ over a preorder, the list
returned by the quadratic longest-increasing-subsequence program on $xs$ is a subsequence of $xs$,
is strictly increasing (each element strictly less than every later one), and is at least as long
as every strictly increasing subsequence of $xs$. -/
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

/-- **The quadratic LIS program attains the optimal length.** For every list $xs$ over a preorder,
the length of the list returned by the quadratic longest-increasing-subsequence program on $xs$ is
the length of a longest strictly increasing subsequence of $xs$. -/
theorem isLISLength_longestIncreasingSubsequence (xs : List α) :
    IsLISLength xs (longestIncreasingSubsequence xs).ret.length :=
  ⟨⟨_, longestIncreasingSubsequence_sublist xs, longestIncreasingSubsequence_pairwise xs, rfl⟩,
    fun _ hys hpair => length_le_longestIncreasingSubsequence hys hpair⟩

omit [DecidableLT α] in
/-- **Uniqueness of the longest increasing subsequence length.** For every list $xs$ of elements
of a preorder and all natural numbers $k$ and $k'$, if both $k$ and $k'$ are the length of a
longest strictly increasing subsequence of $xs$, then $k = k'$. -/
theorem IsLISLength.unique {xs : List α} {k k' : ℕ} (h : IsLISLength xs k)
    (h' : IsLISLength xs k') : k = k' := by
  obtain ⟨ys, hys, hpair, rfl⟩ := h.1
  obtain ⟨ys', hys', hpair', rfl⟩ := h'.1
  exact le_antisymm (h'.2 ys hys hpair) (h.2 ys' hys' hpair')

/-- **Correctness of the quadratic LIS program, by length.** For every list $xs$ over a preorder
and every natural number $k$, the list returned by the quadratic longest-increasing-subsequence
program on $xs$ has length $k$ if and only if $k$ is the length of a longest strictly increasing
subsequence of $xs$. -/
theorem length_longestIncreasingSubsequence_eq_iff (xs : List α) (k : ℕ) :
    (longestIncreasingSubsequence xs).ret.length = k ↔ IsLISLength xs k :=
  ⟨fun h => h ▸ isLISLength_longestIncreasingSubsequence xs,
    fun h => (isLISLength_longestIncreasingSubsequence xs).unique h⟩

end Cslib.Algorithms.Lean.TimeM
