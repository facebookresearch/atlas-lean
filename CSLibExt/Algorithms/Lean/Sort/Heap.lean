/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap

/-!
# Heap sort

This module implements immutable heap sort by inserting every input into the verified binary
min-heap and repeatedly extracting its minimum. The correctness proof uses only the public
`MinHeap` order and multiset API.

With constant-time comparisons and array access, amortized constant-time array growth, and the
usual logarithmic bounds for `MinHeap.push` and `MinHeap.extractMin`, this implementation takes
`O(n log n)` time and `O(n)` additional space. The build phase uses repeated insertion rather than
linear-time bottom-up heap construction. These cost bounds are documented assumptions, not
machine-checked claims of this module.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u} [LinearOrder α]

private theorem foldl_push_elements (xs : List α) (heap : MinHeap α) :
    (xs.foldl (fun current value => current.push value) heap).elements =
      (↑xs : Multiset α) + heap.elements := by
  induction xs generalizing heap with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, heap.elements_push]
      rw [show (↑(x :: xs) : Multiset α) = x ::ₘ (↑xs : Multiset α) from rfl,
        Multiset.cons_add, Multiset.add_cons]

/-- Sort a list in nondecreasing order by repeated insertion into and extraction from a binary
min-heap. -/
def heapSort (xs : List α) : List α :=
  let heap := xs.foldl (fun current value => current.push value) MinHeap.empty
  let rec loop : Nat → MinHeap α → List α
    | 0, _ => []
    | fuel + 1, current =>
        match current.extractMin with
        | none => []
        | some (minimum, rest) => minimum :: loop fuel rest
  loop heap.data.size heap

private theorem heapSort_loop_correct (fuel : Nat) (heap : MinHeap α)
    (hsize : heap.data.size = fuel) :
    List.Pairwise (fun x y => x ≤ y) (heapSort.loop fuel heap) ∧
      (↑(heapSort.loop fuel heap) : Multiset α) = heap.elements := by
  induction fuel generalizing heap with
  | zero =>
      have hdata : heap.data = #[] := Array.size_eq_zero_iff.mp hsize
      simp [heapSort.loop, MinHeap.elements, hdata]
  | succ fuel ih =>
      cases hresult : heap.extractMin with
      | none =>
          have hempty := heap.extractMin_eq_none_iff.mp hresult
          omega
      | some result =>
          rcases result with ⟨minimum, rest⟩
          have helements := heap.extractMin_cons_elements hresult
          have hcard := congrArg Multiset.card helements
          have hrestSize : rest.data.size = fuel := by
            simp [MinHeap.elements] at hcard
            omega
          obtain ⟨hrestSorted, hrestElements⟩ := ih rest hrestSize
          have hminimum : ∀ y ∈ heapSort.loop fuel rest, minimum ≤ y := by
            intro y hy
            apply heap.extractMin_le hresult
            rw [← helements, ← hrestElements]
            simp [hy]
          simp only [heapSort.loop, hresult]
          exact ⟨List.pairwise_cons.2 ⟨hminimum, hrestSorted⟩, by
            change minimum ::ₘ (↑(heapSort.loop fuel rest) : Multiset α) = heap.elements
            rw [hrestElements]
            exact helements⟩

/-- Heap sort preserves every input occurrence, including duplicates. -/
theorem heapSort_multiset (xs : List α) :
    (↑(heapSort xs) : Multiset α) = (↑xs : Multiset α) := by
  let heap := xs.foldl (fun current value => current.push value) MinHeap.empty
  have hcorrect := heapSort_loop_correct heap.data.size heap rfl
  have helements := foldl_push_elements xs (MinHeap.empty : MinHeap α)
  have hresult : (↑(heapSort.loop heap.data.size heap) : Multiset α) =
      (↑xs : Multiset α) := by
    exact hcorrect.2.trans (by simpa [heap, MinHeap.empty, MinHeap.elements] using helements)
  simpa only [heapSort, heap] using hresult

/-- Heap sort returns a permutation of its input. -/
theorem heapSort_perm (xs : List α) : List.Perm (heapSort xs) xs :=
  Multiset.coe_eq_coe.mp (heapSort_multiset xs)

/-- Heap sort returns its output in nondecreasing order. -/
theorem heapSort_sorted (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (heapSort xs) := by
  let heap := xs.foldl (fun current value => current.push value) MinHeap.empty
  have hcorrect := heapSort_loop_correct heap.data.size heap rfl
  simpa only [heapSort, heap] using hcorrect.1

/-- Heap sort refines the standard sorted-permutation specification. -/
theorem heapSort_correct (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (heapSort xs) ∧ List.Perm (heapSort xs) xs :=
  ⟨heapSort_sorted xs, heapSort_perm xs⟩

end Cslib.Algorithms.Lean
