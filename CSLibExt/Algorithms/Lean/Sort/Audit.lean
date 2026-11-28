/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Counting
public import CSLibExt.Algorithms.Lean.Sort.Radix
public import CSLibExt.Algorithms.Lean.Selection.MedianOfMedians
public import Cslib.Algorithms.Lean.MergeSort.MergeSort
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Bounds

/-!
# Sorting and selection library audit

Lane-facing restatements of the library sorting and selection results.
For each algorithm the adapter records the correctness statement and
the per-input cost bound the library proves, with one selection: the
radix adapter leaves out the provider's numeric-order conjunct. The
charged
primitive named in each module's own `Cost model` note. No new sorting
proofs are added here.

## Cost model

Each adapter inherits its library module's declared charge. Merge sort
charges one per order comparison (`TimeM` ticks). Counting and radix
sort charge one per counter initialization, key evaluation, counter
read, counter write, and output write. Median-of-medians charges one
per order comparison. Bounds are stated per concrete input; there is
no worst-case functional and no machine-time claim.

## Gate report

The library proves the upper bounds adapted above. A matching
lower bound exists in cslib's query model:
`Cslib.Query.mergeSort_lowerBound` gives worst-case query complexity
at least `⌈log₂(n!)⌉` (over infinite element types) for the same underlying
`List.mergeSortM`,
which is `Ω(n log n)`. It is stated in the `FreeM` query-cost
model, not in `TimeM` ticks, and no bridge between the two charge
models is claimed here. No expected-cost refinement of these
per-input bounds is claimed.

## References

* Cormen, Leiserson, Rivest, Stein, Introduction to Algorithms, 4th ed.,
  §8.2 (counting sort) and §9.3 (linear-time selection).
-/

public section

universe u

namespace Cslib.Algorithms.Lean.TimeM

open List

/-- **Merge sort is correct.** `mergeSort` returns a sorted permutation of its input. -/
theorem mergeSort_sorted_perm {α : Type} [LinearOrder α] (xs : List α) :
    List.Pairwise (· ≤ ·) ⟪mergeSort xs⟫ ∧ ⟪mergeSort xs⟫ ~ xs := by
  exact mergeSort_correct xs

/-- **Merge sort comparison bound.** `mergeSort` on a list of length `n` charges at most
`n * Nat.clog 2 n` order comparisons. -/
theorem mergeSort_comparisons_le {α : Type} [LinearOrder α] (xs : List α) :
    (mergeSort xs).time ≤ xs.length * Nat.clog 2 xs.length := by
  exact (mergeSort_time_le xs).trans (timeMergeSortRec_le xs.length)

/-- **Counting sort is correct.** `countingSort` returns a sorted stable permutation of its
input. -/
theorem countingSort_stable_sorted_perm {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) :
    List.Pairwise (fun x y => key x ≤ key y) (countingSort key input).ret.toList ∧
      List.Perm (countingSort key input).ret.toList input.toList ∧
      ∀ q : Fin k,
        (countingSort key input).ret.toList.filter (fun x => key x == q) =
          input.toList.filter fun x => key x == q := by
  exact countingSort_correct key input

/-- **Counting sort linear bound.** `countingSort` on `n` records with `k` counters charges at
most `7 * n + 3 * k` operations. -/
theorem countingSort_linear_time {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) :
    (countingSort key input).time ≤ 7 * input.size + 3 * k := by
  exact countingSort_time key input

/-- **Radix sort is correct.** `radixSort` returns a sorted stable permutation of its input.
The provider's fourth conjunct (order by the base-`b` number the digits spell) is not restated
here. -/
theorem radixSort_stable_sorted_perm {α : Type u} {b d : Nat}
    (digits : α → _root_.Vector (Fin b) d) (input : Array α) (hb : 2 ≤ b) :
    List.Pairwise (fun x y => digits x ≤ digits y) (radixSort digits input hb).ret.toList ∧
      List.Perm (radixSort digits input hb).ret.toList input.toList ∧
      ∀ v : _root_.Vector (Fin b) d,
        (radixSort digits input hb).ret.toList.filter (fun x => digits x == v) =
          input.toList.filter fun x => digits x == v := by
  have h := radixSort_correct digits input hb
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- **Radix sort linear bound.** `radixSort` on `n` records with `d` base-`b` digits charges at
most `d * (7 * n + 3 * b)` operations. -/
theorem radixSort_linear_time {α : Type u} {b d : Nat} (digits : α → _root_.Vector (Fin b) d)
    (input : Array α) (hb : 2 ≤ b) :
    (radixSort digits input hb).time ≤ d * (7 * input.size + 3 * b) := by
  exact radixSort_time digits input hb

/-- **Median-of-medians rank.** `medianOfMedians` returns an element of rank `k`. -/
theorem medianOfMedians_rank {α : Type u} [LinearOrder α] {xs : List α} {k : Nat}
    {x : α} (hresult : (medianOfMedians xs k).ret = some x) :
    x ∈ xs ∧ xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) := by
  exact medianOfMedians_correct hresult

/-- **Median-of-medians linear bound.** `medianOfMedians` on a list of length `n` charges at
most `80 * n` order comparisons. -/
theorem medianOfMedians_linear_time {α : Type u} [LinearOrder α] (xs : List α)
    (k : Nat) :
    (medianOfMedians xs k).time ≤ 80 * xs.length := by
  exact medianOfMedians_time xs k

/-- **Ceil-log factorial bound.** `clog_factorial_le` restates
`Cslib.Query.clog_factorial_le_mul_clog`. -/
theorem clog_factorial_le (n : Nat) :
    Nat.clog 2 (Nat.factorial n) ≤ n * Nat.clog 2 n := by
  exact Cslib.Query.clog_factorial_le_mul_clog n

end Cslib.Algorithms.Lean.TimeM
