/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.LongestIncreasingSubsequence
public import CSLibExt.Algorithms.Lean.Search.LowerBound
public import Mathlib.Data.List.Basic

/-!
# Longest increasing subsequence length by patience sorting

The `O(n log n)` algorithm for the length of a longest strictly increasing subsequence (CLRS,
third edition, Exercise 15.4-6; Fredman 1975). Scan the input keeping an array `tails` whose entry
`k` is the smallest last element of a strictly increasing subsequence of length `k + 1` seen so
far. The array is strictly increasing, so each new element `x` finds by binary search the first
entry `≥ x` (`lowerBound`) and replaces it, or extends the array when every entry is `< x`. The
final size is the answer.

`patienceLength_spec` proves that the size is the length of a longest strictly increasing
subsequence, in the sense `IsLISLength` of the quadratic module
(`CSLibExt.Algorithms.Lean.DynamicProgramming.LongestIncreasingSubsequence`), so the two
algorithms agree (`patienceLength_eq_length_longestIncreasingSubsequence`). Values come from a
linear order in `Type` (binary search needs the total order).

## Cost model

The comparisons of the binary searches, as in `lowerBound`: inserting into an array of size `m`
costs at most `⌈log₂ (m + 1)⌉`. Array updates are free. A list of length `n` costs at most
`n * ⌈log₂ (n + 1)⌉` (`patienceLength_time_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

open scoped List

variable {α : Type} [LinearOrder α]

/-- **Patience step.** Given an array $t$ of tails and an element $x$ over a linear order, let $i$
be the index returned by the lower-bound binary search for $x$ in $t$. If $i$ is less than the
size of $t$, the step replaces the entry of $t$ at index $i$ by $x$; otherwise it appends $x$ to
$t$. Its cost is the number of comparisons made by the binary search.

When $t$ is sorted increasingly, as it stays throughout the patience scan from the empty array,
$i$ is the first index whose entry is at least $x$, so the step replaces the first entry $\ge x$,
or appends $x$ if there is none. On unsorted input $i$ need not be the first such index. -/
def patienceStep (tails : Array α) (x : α) : TimeM ℕ (Array α) := do
  let i ← lowerBound tails x
  if h : i < tails.size then pure (tails.set i x h) else pure (tails.push x)

/-- **Patience scan.** Given an array of tails and a list over a linear order, the patience scan
applies the patience step to the elements of the list in order: on the empty list it returns the
tails unchanged, and on a list $x$ followed by $xs$ it applies the patience step for $x$ to the
tails and then runs the patience scan of $xs$ from the result. Its cost is the total cost of the
steps. -/
def patienceScan : Array α → List α → TimeM ℕ (Array α)
  | tails, [] => pure tails
  | tails, x :: xs => do
      let t ← patienceStep tails x
      patienceScan t xs

/-- **Patience sorting.** Given a list $xs$ over a linear order, patience sorting runs the patience
scan of $xs$ starting from the empty array of tails and returns the size of the resulting array.
Its cost is the number of comparisons made by the scan. -/
def patienceLength (xs : List α) : TimeM ℕ ℕ := do
  let t ← patienceScan #[] xs
  pure t.size

/-! ## The step on lists -/

/-- Replace position `i` by `x`; at `i = t.length` this appends. -/
private def replaceAt (t : List α) (i : ℕ) (x : α) : List α := t.take i ++ x :: t.drop (i + 1)

private theorem patienceStep_ret_toList (tails : Array α) (x : α) :
    (patienceStep tails x).ret.toList =
      replaceAt tails.toList (lowerBound tails x).ret x := by
  simp only [patienceStep, ret_bind]
  split_ifs with h
  · simp [replaceAt, Array.toList_set, List.set_eq_take_append_cons_drop, h]
  · have hle := (lowerBound tails x).ret
    simp only [ret_pure, Array.toList_push, replaceAt]
    have hge : tails.size ≤ (lowerBound tails x).ret := Nat.le_of_not_lt h
    rw [List.take_of_length_le (by simpa using hge),
      List.drop_of_length_le (by simp; omega)]

omit [LinearOrder α] in
private theorem length_replaceAt {t : List α} {i : ℕ} (x : α) (hi : i ≤ t.length) :
    (replaceAt t i x).length = max t.length (i + 1) := by
  simp only [replaceAt, List.length_append, List.length_take, List.length_cons, List.length_drop]
  omega

omit [LinearOrder α] in
private theorem getElem_replaceAt_lt {t : List α} {i j : ℕ} (x : α) (hji : j < i)
    (hi : i ≤ t.length)
    (hj : j < (replaceAt t i x).length) :
    (replaceAt t i x)[j] = t[j]'(by omega) := by
  simp only [replaceAt]
  rw [List.getElem_append_left (by simp; omega), List.getElem_take]

omit [LinearOrder α] in
private theorem getElem_replaceAt_self {t : List α} {i : ℕ} (x : α) (hi : i ≤ t.length)
    (hj : i < (replaceAt t i x).length) :
    (replaceAt t i x)[i] = x := by
  simp only [replaceAt]
  rw [List.getElem_append_right (by simp)]
  simp [List.length_take, Nat.min_eq_left hi]

omit [LinearOrder α] in
private theorem getElem_replaceAt_gt {t : List α} {i j : ℕ} (x : α) (hij : i < j)
    (hi : i ≤ t.length)
    (hj : j < (replaceAt t i x).length) :
    (replaceAt t i x)[j] = t[j]'(by rw [length_replaceAt x hi] at hj; omega) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
  simp only [replaceAt]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_take, Nat.min_eq_left hi, Nat.add_sub_cancel_left,
    List.getElem_cons_succ, List.getElem_drop]
  congr 1
  omega

/-! ## The invariant -/

/-- **Patience sorting invariant.** For lists $P$ and $t = (t_0, \dots, t_{m-1})$ over a linear
order, the invariant holds for the processed prefix $P$ and the tails $t$ when three conditions
hold: $t$ is strictly increasing; for every $k < m$ some strictly increasing subsequence of $P$ of
length $k + 1$ has last element $t_k$; and every nonempty strictly increasing subsequence of $P$,
of length $\ell$ and with last element $y$, satisfies $\ell \le m$ and $t_{\ell - 1} \le y$. -/
structure PatienceInv (P t : List α) : Prop where
  sorted : t.Pairwise (· < ·)
  witness : ∀ k (hk : k < t.length), ∃ ys, ys <+ P ∧ ys.Pairwise (· < ·) ∧
    ys.length = k + 1 ∧ ys.getLast? = some t[k]
  bound : ∀ ys y, ys <+ P → ys.Pairwise (· < ·) → ys.getLast? = some y →
    ∃ h : ys.length - 1 < t.length, t[ys.length - 1] ≤ y

theorem patienceInv_nil : PatienceInv ([] : List α) [] where
  sorted := List.Pairwise.nil
  witness k hk := absurd hk (Nat.not_lt_zero _)
  bound ys y hys _ hy := by
    rw [List.sublist_nil.1 hys] at hy
    simp at hy

omit [LinearOrder α] in
private theorem le_of_mem_of_getLast? {ys : List α} [Preorder α] {a y : α}
    (hp : ys.Pairwise (· < ·)) (hy : ys.getLast? = some y) (ha : a ∈ ys) : a ≤ y := by
  obtain ⟨zs, rfl⟩ := List.getLast?_eq_some_iff.1 hy
  rcases List.mem_append.1 ha with ha | ha
  · exact le_of_lt ((List.pairwise_append.1 hp).2.2 a ha y List.mem_cons_self)
  · rw [List.mem_singleton.1 ha]

/-- One step preserves the invariant, given the lower-bound index `i` of `x` in `t`. -/
private theorem PatienceInv.step {P t : List α} (h : PatienceInv P t) (x : α) {i : ℕ}
    (hi : i ≤ t.length) (hlt : ∀ j, j < i → ∀ (hjt : j < t.length), t[j] < x)
    (hge : ∀ j, i ≤ j → ∀ (hjt : j < t.length), x ≤ t[j]) :
    PatienceInv (P ++ [x]) (replaceAt t i x) := by
  have hlen := length_replaceAt x hi
  have hsort := List.pairwise_iff_getElem.1 h.sorted
  constructor
  · -- strictly increasing
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    rcases lt_trichotomy a i with hai | rfl | hai
    · rw [getElem_replaceAt_lt x hai hi]
      rcases lt_trichotomy b a with hba | rfl | hba
      · omega
      · omega
      rcases lt_trichotomy b i with hbi | rfl | hbi
      · rw [getElem_replaceAt_lt x hbi hi]
        exact hsort _ _ _ _ hab
      · rw [getElem_replaceAt_self x hi]
        exact hlt a hai _
      · rw [getElem_replaceAt_gt x hbi hi]
        exact hsort _ _ _ _ hab
    · rw [getElem_replaceAt_self x hi, getElem_replaceAt_gt x hab hi]
      have hat : a < t.length := by omega
      exact lt_of_le_of_lt (hge a le_rfl hat) (hsort _ _ _ _ hab)
    · rw [getElem_replaceAt_gt x hai hi, getElem_replaceAt_gt x (hai.trans hab) hi]
      exact hsort _ _ _ _ hab
  · -- witnesses
    intro k hk
    rcases lt_trichotomy k i with hki | rfl | hki
    · obtain ⟨ys, hs, hp, hl, hlast⟩ := h.witness k (by omega)
      refine ⟨ys, hs.trans (List.sublist_append_left P [x]), hp, hl, ?_⟩
      rw [getElem_replaceAt_lt x hki hi]
      exact hlast
    · rw [getElem_replaceAt_self x hi]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨[x], List.singleton_sublist.2 (List.mem_append_right P (List.mem_singleton_self x)),
          List.pairwise_singleton _ _, rfl, rfl⟩
      · obtain ⟨ys, hs, hp, hl, hlast⟩ := h.witness (k - 1) (by omega)
        have hlast' := hlt (k - 1) (by omega) (by omega)
        refine ⟨ys ++ [x], hs.append (List.Sublist.refl [x]), ?_, by simp [hl]; omega, by simp⟩
        rw [List.pairwise_append]
        exact ⟨hp, List.pairwise_singleton _ _, fun a ha b hb => by
          rw [List.mem_singleton.1 hb]
          exact lt_of_le_of_lt (le_of_mem_of_getLast? hp hlast ha) hlast'⟩
    · obtain ⟨ys, hs, hp, hl, hlast⟩ := h.witness k (by omega)
      refine ⟨ys, hs.trans (List.sublist_append_left P [x]), hp, hl, ?_⟩
      rw [getElem_replaceAt_gt x hki hi]
      exact hlast
  · -- bound
    intro ys y hys hp hy
    obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 hys
    rcases List.sublist_singleton.1 h₂ with rfl | rfl
    · rw [List.append_nil] at hy hp ⊢
      obtain ⟨hm, hle⟩ := h.bound r₁ y h₁ hp hy
      refine ⟨by omega, ?_⟩
      rcases lt_trichotomy (r₁.length - 1) i with hm' | hm' | hm'
      · rwa [getElem_replaceAt_lt x hm' hi]
      · simp only [hm', getElem_replaceAt_self x hi]
        exact (hge i le_rfl (by omega)).trans (by simpa [hm'] using hle)
      · rwa [getElem_replaceAt_gt x hm' hi]
    · have hyx : y = x := by simpa using hy.symm
      subst hyx
      have hp₁ : r₁.Pairwise (· < ·) := (List.pairwise_append.1 hp).1
      have hlt₁ : ∀ a ∈ r₁, a < y := fun a ha =>
        (List.pairwise_append.1 hp).2.2 a ha y (List.mem_singleton_self y)
      -- every new entry at or below `i` is at most `y`
      have key : ∀ m (hm : m < (replaceAt t i y).length), m ≤ i → (replaceAt t i y)[m] ≤ y := by
        intro m hm hmi
        rcases Nat.lt_or_ge m i with hmi' | hmi'
        · rw [getElem_replaceAt_lt y hmi' hi]
          exact le_of_lt (hlt m hmi' _)
        · obtain rfl : m = i := by omega
          rw [getElem_replaceAt_self y hi]
      rcases List.eq_nil_or_concat r₁ with rfl | ⟨r, z, rfl⟩
      · exact ⟨by simp; omega, key _ _ (by simp)⟩
      · rw [List.concat_eq_append] at *
        have hz : z < y := hlt₁ z (by simp)
        obtain ⟨hm, hle⟩ := h.bound (r ++ [z]) z h₁ hp₁ (by simp)
        have hmi : (r ++ [z]).length - 1 < i := by
          by_contra hcon
          exact absurd (lt_of_le_of_lt (hge _ (by omega) hm) (lt_of_le_of_lt hle hz)) (lt_irrefl _)
        simp only [List.length_append, List.length_singleton] at hmi
        exact ⟨by simp; omega, key _ _ (by simp; omega)⟩

/-! ## Correctness -/

/-- **The patience scan preserves the invariant.** Let $P$ be a list and $t$ an array of tails over
a linear order such that the patience sorting invariant holds for $P$ and the entries of $t$. Then
for every list $xs$, the invariant holds for $P$ followed by $xs$ and the entries of the array
returned by the patience scan of $xs$ from $t$. -/
theorem PatienceInv.scan {P : List α} {tails : Array α} (h : PatienceInv P tails.toList)
    (xs : List α) : PatienceInv (P ++ xs) (patienceScan tails xs).ret.toList := by
  induction xs generalizing P tails with
  | nil => simpa [patienceScan] using h
  | cons x xs ih =>
      simp only [patienceScan, ret_bind]
      rw [show P ++ x :: xs = (P ++ [x]) ++ xs by simp]
      apply ih
      rw [patienceStep_ret_toList]
      have hs : tails.Pairwise (fun a b => a ≤ b) := by
        rw [Array.pairwise_iff_getElem]
        intro i j hi hj hij
        rw [← Array.getElem_toList (by simpa using hi),
          ← Array.getElem_toList (by simpa using hj)]
        exact List.pairwise_iff_getElem.mp
          (h.sorted.imp (fun hab => le_of_lt hab)) i j (by simpa using hi)
          (by simpa using hj) hij
      obtain ⟨hi, hlt, hge⟩ := lowerBound_spec tails x hs
      refine h.step x (by simpa using hi) (fun j hj hjt => ?_) (fun j hj hjt => ?_)
      · simpa using hlt j hj (by simpa using hjt)
      · simpa using hge j hj (by simpa using hjt)

/-- **Correctness of patience sorting.** For every list $xs$ over a linear order, the value
returned by patience sorting on $xs$ is the length of a longest strictly increasing subsequence of
$xs$: some strictly increasing subsequence of $xs$ has this length, and no strictly increasing
subsequence of $xs$ is longer. -/
theorem patienceLength_spec (xs : List α) : IsLISLength xs (patienceLength xs).ret := by
  have h := patienceInv_nil.scan (tails := #[]) xs
  simp only [List.nil_append] at h
  simp only [patienceLength, ret_bind, ret_pure]
  set t := (patienceScan #[] xs).ret
  have hsize : t.size = t.toList.length := by simp
  refine ⟨?_, fun ys hys hp => ?_⟩
  · rcases Nat.eq_zero_or_pos t.size with h0 | h0
    · exact ⟨[], List.nil_sublist _, List.Pairwise.nil, by simp [h0]⟩
    · obtain ⟨ys, hs, hp, hl, -⟩ := h.witness (t.size - 1) (by omega)
      exact ⟨ys, hs, hp, by omega⟩
  · rcases List.eq_nil_or_concat ys with rfl | ⟨r, z, rfl⟩
    · simp
    · obtain ⟨hm, -⟩ := h.bound _ z hys hp (by simp)
      simp only [List.concat_eq_append, List.length_append, List.length_singleton] at hm ⊢
      omega

/-- **Patience sorting agrees with the quadratic dynamic program.** For every list $xs$ over a
linear order, the value returned by patience sorting on $xs$ equals the length of the list
returned on $xs$ by the quadratic dynamic program for a longest strictly increasing subsequence. -/
theorem patienceLength_eq_length_longestIncreasingSubsequence (xs : List α) :
    (patienceLength xs).ret = (longestIncreasingSubsequence xs).ret.length :=
  ((length_longestIncreasingSubsequence_eq_iff xs _).2 (patienceLength_spec xs)).symm

/-! ## Cost -/

/-- **A patience step grows the tails by at most one.** Let $\alpha$ be a linear order. For every
array $t$ over $\alpha$ and every element $x \in \alpha$, the array returned by the patience step
for $x$ on $t$ has size at most the size of $t$ plus $1$. -/
theorem patienceStep_size_le (tails : Array α) (x : α) :
    (patienceStep tails x).ret.size ≤ tails.size + 1 := by
  simp only [patienceStep, ret_bind]
  split_ifs <;> simp

theorem patienceStep_time_le (tails : Array α) (x : α) :
    (patienceStep tails x).time ≤ Nat.clog 2 (tails.size + 1) := by
  simp only [patienceStep, time_bind]
  split_ifs <;> simpa using lowerBound_time_le tails x

theorem patienceScan_le (tails : Array α) (xs : List α) :
    (patienceScan tails xs).ret.size ≤ tails.size + xs.length ∧
      (patienceScan tails xs).time ≤ xs.length * Nat.clog 2 (tails.size + xs.length + 1) := by
  induction xs generalizing tails with
  | nil => simp [patienceScan]
  | cons x xs ih =>
      simp only [patienceScan, ret_bind, time_bind, List.length_cons]
      obtain ⟨ih1, ih2⟩ := ih (patienceStep tails x).ret
      have hs := patienceStep_size_le tails x
      have ht := patienceStep_time_le tails x
      refine ⟨by omega, ?_⟩
      have h1 : Nat.clog 2 (tails.size + 1) ≤ Nat.clog 2 (tails.size + (xs.length + 1) + 1) :=
        Nat.clog_mono_right 2 (by omega)
      have h2 : Nat.clog 2 ((patienceStep tails x).ret.size + xs.length + 1) ≤
          Nat.clog 2 (tails.size + (xs.length + 1) + 1) := Nat.clog_mono_right 2 (by omega)
      have h3 := Nat.mul_le_mul_left xs.length h2
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- **Comparison bound for patience sorting.** For every list $xs$ of length $n$ over a linear
order, patience sorting on $xs$ uses at most $n \lceil \log_2 (n + 1) \rceil$ comparisons. -/
theorem patienceLength_time_le (xs : List α) :
    (patienceLength xs).time ≤ xs.length * Nat.clog 2 (xs.length + 1) := by
  simpa [patienceLength] using (patienceScan_le #[] xs).2

end Cslib.Algorithms.Lean.TimeM
