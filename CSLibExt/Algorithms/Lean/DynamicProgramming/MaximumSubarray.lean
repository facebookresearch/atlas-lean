/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

/-!
# Maximum subarray: Kadane's linear scan

The maximum-subarray problem of CLRS, third edition, Section 4.1, asks for a nonempty
contiguous run of the input with the largest sum. Exercise 4.1-5 there, and Bentley,
"Programming Pearls: Algorithm Design Techniques", CACM 27(9), 1984, credit Kadane with the
linear-time scan formalized here: after reading element `x`, the best sum of a nonempty run
ending at `x` is `max x (ending + x)`, and the answer is the largest such value seen.

Contiguous runs are `List.IsInfix` (`<:+:`). `IsMaxSubarraySum xs m` says that `m` is the sum
of some nonempty run of `xs` and bounds the sum of every nonempty run. Runs are nonempty, as in
CLRS, so an all-negative input returns its largest element, not the empty-run sum `0`. The scan
returns `none` on the empty list and the maximum sum otherwise; it does not report the run's
endpoints.

The values live in any linearly ordered additive monoid in which adding on the right is
monotone; `ℤ`, `ℚ` and `ℝ` are instances. No commutativity is needed.

## Cost model

Each element after the first costs three units: the addition `ending + x` and the two
comparisons hidden in the two `max` updates. Reading the first element, pattern matching,
recursion, and building the result are free. A list of length `n ≥ 1` costs exactly
`3 * (n - 1)`; the empty list costs `0`. This is an operation count over the value type; it
says nothing about bit cost or stack space.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [AddMonoid α] [LinearOrder α]

/-- `m` is the maximum sum of a nonempty contiguous run of `xs`: some nonempty run sums to `m`,
and every nonempty run sums to at most `m`. -/
def IsMaxSubarraySum (xs : List α) (m : α) : Prop :=
  (∃ ys, ys <:+: xs ∧ ys ≠ [] ∧ ys.sum = m) ∧ ∀ ys, ys <:+: xs → ys ≠ [] → ys.sum ≤ m

/-- `e` is the maximum sum of a nonempty suffix of `xs`, i.e. of a run ending at its last
element. This is the scan's invariant for its `ending` accumulator. -/
def IsMaxSuffixSum (xs : List α) (e : α) : Prop :=
  (∃ ys, ys <:+ xs ∧ ys ≠ [] ∧ ys.sum = e) ∧ ∀ ys, ys <:+ xs → ys ≠ [] → ys.sum ≤ e

/-- Kadane's scan over the unread elements. `ending` is the best sum of a nonempty run ending at
the last element read and `best` is the best sum of any nonempty run read so far. -/
def kadaneScan (ending best : α) : List α → TimeM ℕ α
  | [] => pure best
  | x :: xs => do
      ✓[3]
      let ending' := max x (ending + x)
      kadaneScan ending' (max best ending') xs

/-- Kadane's algorithm: the maximum sum of a nonempty contiguous run, or `none` for the empty
list. The first element seeds both accumulators. -/
def maxSubarraySum : List α → TimeM ℕ (Option α)
  | [] => pure none
  | x :: xs => some <$> kadaneScan x x xs

/-! ## Cost -/

@[simp]
theorem kadaneScan_time (ending best : α) (xs : List α) :
    (kadaneScan ending best xs).time = 3 * xs.length := by
  induction xs generalizing ending best with
  | nil => simp [kadaneScan]
  | cons x xs ih =>
      simp only [kadaneScan, time_bind, time_tick, ih, List.length_cons]
      omega

/-- Kadane's scan performs exactly three operations per element after the first. -/
@[simp]
theorem maxSubarraySum_time (xs : List α) :
    (maxSubarraySum xs).time = 3 * (xs.length - 1) := by
  cases xs with
  | nil => simp [maxSubarraySum]
  | cons x xs => simp [maxSubarraySum]

/-! ## The specification -/

theorem IsMaxSubarraySum.ne_nil {xs : List α} {m : α} (h : IsMaxSubarraySum xs m) :
    xs ≠ [] := by
  rintro rfl
  obtain ⟨ys, hys, hne, -⟩ := h.1
  exact hne (List.eq_nil_of_infix_nil hys)

/-- The maximum subarray sum is unique. -/
theorem IsMaxSubarraySum.unique {xs : List α} {m m' : α} (h : IsMaxSubarraySum xs m)
    (h' : IsMaxSubarraySum xs m') : m = m' := by
  obtain ⟨ys, hys, hne, rfl⟩ := h.1
  obtain ⟨ys', hys', hne', rfl⟩ := h'.1
  exact le_antisymm (h'.2 ys hys hne) (h.2 ys' hys' hne')

theorem isMaxSuffixSum_singleton (x : α) : IsMaxSuffixSum [x] x := by
  refine ⟨⟨[x], List.suffix_refl _, by simp, by simp⟩, fun ys hys hne => ?_⟩
  rcases List.suffix_cons_iff.1 hys with rfl | hys
  · simp
  · exact absurd (List.eq_nil_of_suffix_nil hys) hne

theorem isMaxSubarraySum_singleton (x : α) : IsMaxSubarraySum [x] x := by
  refine ⟨⟨[x], List.infix_refl _, by simp, by simp⟩, fun ys hys hne => ?_⟩
  rcases List.infix_cons_iff.1 hys with hys | hys
  · rcases List.prefix_cons_iff.1 hys with rfl | ⟨t, rfl, ht⟩
    · exact absurd rfl hne
    · simp [List.eq_nil_of_prefix_nil ht]
  · exact absurd (List.eq_nil_of_infix_nil hys) hne

/-- Appending `x` updates the best run ending at the last element to `max x (e + x)`: either the
run is `[x]` alone, or it extends a best run ending just before `x`. -/
theorem IsMaxSuffixSum.concat [AddRightMono α] {pre : List α} {e : α}
    (h : IsMaxSuffixSum pre e) (x : α) : IsMaxSuffixSum (pre ++ [x]) (max x (e + x)) := by
  obtain ⟨⟨t, ht, htne, rfl⟩, hle⟩ := h
  refine ⟨?_, fun ys hys hne => ?_⟩
  · rcases le_total (t.sum + x) x with hx | hx
    · exact ⟨[x], List.suffix_append _ _, by simp, by simp [max_eq_left hx]⟩
    · exact ⟨t ++ [x], List.suffix_concat_iff.2 (Or.inr ⟨t, rfl, ht⟩), by simp,
        by simp [max_eq_right hx]⟩
  · rcases List.suffix_concat_iff.1 hys with rfl | ⟨s, rfl, hs⟩
    · exact absurd rfl hne
    · rw [List.sum_append, List.sum_singleton]
      by_cases hs0 : s = []
      · subst hs0
        simp
      · exact le_max_of_le_right (add_le_add_left (hle s hs hs0) x)

/-- Appending `x` updates the best run overall to the larger of the old best and the new best
run ending at `x`. -/
theorem IsMaxSubarraySum.concat [AddRightMono α] {pre : List α} {e b : α}
    (he : IsMaxSuffixSum pre e) (hb : IsMaxSubarraySum pre b) (x : α) :
    IsMaxSubarraySum (pre ++ [x]) (max b (max x (e + x))) := by
  have he' := he.concat x
  obtain ⟨⟨s, hs, hsne, hssum⟩, hsle⟩ := he'
  obtain ⟨⟨t, ht, htne, rfl⟩, htle⟩ := hb
  refine ⟨?_, fun ys hys hne => ?_⟩
  · rcases le_total (max x (e + x)) t.sum with h | h
    · exact ⟨t, ht.trans (List.prefix_append _ _).isInfix, htne,
        (max_eq_left h).symm⟩
    · exact ⟨s, hs.isInfix, hsne, by rw [hssum, max_eq_right h]⟩
  · rcases List.infix_concat_iff.1 hys with hys | hys
    · exact le_max_of_le_right (hsle ys hys hne)
    · exact le_max_of_le_left (htle ys hys hne)

/-! ## Correctness -/

/-- The scan invariant: if the accumulators are the best run ending at the end of the read
prefix and the best run in it, the scan returns the maximum subarray sum of the whole list. -/
theorem kadaneScan_ret [AddRightMono α] {pre : List α} {ending best : α}
    (he : IsMaxSuffixSum pre ending) (hb : IsMaxSubarraySum pre best) (rest : List α) :
    IsMaxSubarraySum (pre ++ rest) (kadaneScan ending best rest).ret := by
  induction rest generalizing pre ending best with
  | nil => simpa [kadaneScan] using hb
  | cons x xs ih =>
      have h := ih (he.concat x) (hb.concat he x)
      simpa only [kadaneScan, ret_bind, List.append_assoc, List.singleton_append] using h

/-- Kadane's algorithm returns a value exactly when the input is nonempty, and that value is the
maximum sum of a nonempty contiguous run. -/
theorem maxSubarraySum_ret_eq_some_iff [AddRightMono α] (xs : List α) (m : α) :
    (maxSubarraySum xs).ret = some m ↔ IsMaxSubarraySum xs m := by
  cases xs with
  | nil =>
      simp only [maxSubarraySum, ret_pure, reduceCtorEq, false_iff]
      exact fun h => h.ne_nil rfl
  | cons x xs =>
      have h := kadaneScan_ret (isMaxSuffixSum_singleton x) (isMaxSubarraySum_singleton x) xs
      simp only [List.singleton_append] at h
      simp only [maxSubarraySum, ret_map, Option.some.injEq]
      exact ⟨fun hm => hm ▸ h, fun hm => h.unique hm⟩

@[simp]
theorem maxSubarraySum_ret_eq_none_iff (xs : List α) :
    (maxSubarraySum xs).ret = none ↔ xs = [] := by
  cases xs <;> simp [maxSubarraySum]

/-- Every nonempty contiguous run sums to at most the returned value. -/
theorem sum_le_of_maxSubarraySum [AddRightMono α] {xs ys : List α} {m : α}
    (hm : (maxSubarraySum xs).ret = some m) (hys : ys <:+: xs) (hne : ys ≠ []) :
    ys.sum ≤ m :=
  ((maxSubarraySum_ret_eq_some_iff xs m).1 hm).2 ys hys hne

/-- Some nonempty contiguous run attains the returned value. -/
theorem exists_sum_eq_of_maxSubarraySum [AddRightMono α] {xs : List α} {m : α}
    (hm : (maxSubarraySum xs).ret = some m) :
    ∃ ys, ys <:+: xs ∧ ys ≠ [] ∧ ys.sum = m :=
  ((maxSubarraySum_ret_eq_some_iff xs m).1 hm).1

end Cslib.Algorithms.Lean.TimeM
