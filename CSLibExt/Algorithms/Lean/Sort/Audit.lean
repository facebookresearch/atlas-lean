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

/-!
# Sorting and selection library audit

Lane-facing restatements of the library sorting and selection results.
For each algorithm the adapter records exactly what the library proves:
the correctness statement and the per-input cost bound, with the charged
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

The library proves the upper bounds adapted below. A matching
information-theoretic `Ω(n log n)` comparison lower bound for merge
sort is not in the library, and no expected-cost refinement of these
per-input bounds is claimed here.

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

/-- **Counting sort linear bound.** `countingSort` on `n` records with `k` counters charges at
most `7 * n + 3 * k` operations. -/
theorem countingSort_linear_time {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) :
    (countingSort key input).time ≤ 7 * input.size + 3 * k := by
  exact countingSort_time key input

/-- **Radix sort linear bound.** `radixSort` on `n` records with `d` base-`b` digits charges at
most `d * (7 * n + 3 * b)` operations. -/
theorem radixSort_linear_time {α : Type u} {b d : Nat} (digits : α → Vector (Fin b) d)
    (input : Array α) (hb : 2 ≤ b) :
    (radixSort digits input hb).time ≤ d * (7 * input.size + 3 * b) := by
  exact radixSort_time digits input hb

/-- **Median-of-medians linear bound.** `medianOfMedians` on a list of length `n` charges at
most `80 * n` order comparisons. -/
theorem medianOfMedians_linear_time {α : Type u} [LinearOrder α] (xs : List α)
    (k : Nat) :
    (medianOfMedians xs k).time ≤ 80 * xs.length := by
  exact medianOfMedians_time xs k

end Cslib.Algorithms.Lean.TimeM
