/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LeftistHeap

/-!
# Leftist-heap executable regression tests

Concrete empty, singleton, odd/even, duplicate, and accumulator cases for
`auto-fdsa-15-04/environment/Task.lean` at pinned source commit
`16412d086eb5af2e74da78731bde50da0667bc79`. All reductions and correctness
checks use the public API and kernel-checked proofs. Cost assertions count
only heap-merge steps, not reversal or other overhead.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LeftistHeapTests

open LHeap

/-- Three singleton heaps; the final heap has a nonempty right spine. -/
def odd : List (LHeap Nat) :=
  [LHeap.singleton 3, LHeap.singleton 1, LHeap.singleton 2]

/-- Four singleton heaps in unsorted order. -/
def even : List (LHeap Nat) :=
  [LHeap.singleton 4, LHeap.singleton 1, LHeap.singleton 3, LHeap.singleton 2]

/-- Repeated values must survive adjacent merging and full construction. -/
def duplicates : List (LHeap Nat) :=
  [LHeap.singleton 2, LHeap.singleton 1, LHeap.singleton 1, LHeap.singleton 2]

/-- A nonempty reversed accumulator with distinct entries. -/
def accumulator : List (LHeap Nat) := [LHeap.singleton 9, LHeap.singleton 8]

example : lheap_list2 ([] : List Nat) = E := by rfl
example : lheap_list2 ([7] : List Nat) = LHeap.singleton 7 := by rfl
example : merge_all ([] : List (LHeap Nat)) = E := by rfl
example : merge_all2 ([] : List (LHeap Nat)) = E := by rfl
example : merge_all2 [LHeap.singleton (7 : Nat)] = LHeap.singleton 7 := by rfl

example : merge_adj ([] : List (LHeap Nat)) = [] := by rfl
example : merge_adj2 [] ([] : List (LHeap Nat)) = [] := by
  simp [merge_adj2]
example : merge_adj2 [] [LHeap.singleton (7 : Nat)] = [LHeap.singleton 7] := by
  simp [merge_adj2]

example : merge_adj2 [] odd =
    [(LHeap.singleton 3).merge (LHeap.singleton 1), LHeap.singleton 2] := by
  simp [odd, merge_adj2]
example : merge_adj2 [] even =
    [(LHeap.singleton 4).merge (LHeap.singleton 1),
      (LHeap.singleton 3).merge (LHeap.singleton 2)] := by
  simp [even, merge_adj2]

/-- The odd pass keeps the unpaired final entry and reconstructs exact ranks. -/
theorem oddResult : merge_all2 odd =
    N 2 1 (LHeap.singleton 3) (LHeap.singleton 2) := by
  simp [odd, merge_all2, merge_all2Aux, merge_adj2, merge, mergeAux,
    make, LHeap.singleton, size, rank]

example : (merge_all2 even).size = 4 := by
  simp [even, merge_all2, merge_all2Aux, merge_adj2, merge, mergeAux,
    make, LHeap.singleton, size, rank]
example : (merge_all2 even).rank = 2 := by
  simp [even, merge_all2, merge_all2Aux, merge_adj2, merge, mergeAux,
    make, LHeap.singleton, size, rank]
example : (merge_all2 duplicates).size = 4 := by
  simp [duplicates, merge_all2, merge_all2Aux, merge_adj2, merge, mergeAux,
    make, LHeap.singleton, size, rank]

example : (E : LHeap Nat).merge (LHeap.singleton 3) = LHeap.singleton 3 := by rfl
example : (LHeap.singleton (3 : Nat)).merge E = LHeap.singleton 3 := by rfl
example : (LHeap.singleton (3 : Nat)).merge (LHeap.singleton 1) =
    N 1 1 (LHeap.singleton 3) E := by rfl
example : make (0 : Nat) E (LHeap.singleton 2) =
    N 1 0 (LHeap.singleton 2) E := by rfl

-- Accumulator entries precede the new pairs, in reverse accumulator order.
example : merge_adj2 accumulator [] =
    [LHeap.singleton 8, LHeap.singleton 9] := by
  simp [accumulator, merge_adj2]
example : merge_adj2 accumulator [LHeap.singleton 7] =
    [LHeap.singleton 8, LHeap.singleton 9, LHeap.singleton 7] := by
  simp [accumulator, merge_adj2]
example : merge_adj2 accumulator odd =
    [LHeap.singleton 8, LHeap.singleton 9,
      (LHeap.singleton 3).merge (LHeap.singleton 1), LHeap.singleton 2] := by
  simp [accumulator, odd, merge_adj2]
example : merge_adj2 accumulator even =
    [LHeap.singleton 8, LHeap.singleton 9,
      (LHeap.singleton 4).merge (LHeap.singleton 1),
      (LHeap.singleton 3).merge (LHeap.singleton 2)] := by
  simp [accumulator, even, merge_adj2]

example : (lheap_list2 ([] : List Nat)).mset_tree = 0 := mset_lheap_list2 []
example : (lheap_list2 ([7] : List Nat)).mset_tree = {7} := mset_lheap_list2 [7]
example : (lheap_list2 ([3, 1, 2] : List Nat)).mset_tree =
    ([3, 1, 2] : Multiset Nat) := mset_lheap_list2 _
example : (lheap_list2 ([4, 1, 3, 2] : List Nat)).mset_tree =
    ([4, 1, 3, 2] : Multiset Nat) := mset_lheap_list2 _
example : Multiset.count 1
    (lheap_list2 ([2, 1, 1, 2] : List Nat)).mset_tree = 2 := by
  rw [mset_lheap_list2]
  rfl
example : Multiset.count 2
    (lheap_list2 ([2, 1, 1, 2] : List Nat)).mset_tree = 2 := by
  rw [mset_lheap_list2]
  rfl

-- Both independent invariants cover all boundary/input classes.
example : (lheap_list2 ([] : List Nat)).heap ∧
    (lheap_list2 ([] : List Nat)).ltree :=
  ⟨heap_lheap_list2 [], ltree_lheap_list2 []⟩
example : (lheap_list2 ([7] : List Nat)).heap ∧
    (lheap_list2 ([7] : List Nat)).ltree :=
  ⟨heap_lheap_list2 _, ltree_lheap_list2 _⟩
example : (lheap_list2 ([3, 1, 2] : List Nat)).heap ∧
    (lheap_list2 ([3, 1, 2] : List Nat)).ltree :=
  ⟨heap_lheap_list2 _, ltree_lheap_list2 _⟩
example : (lheap_list2 ([4, 1, 3, 2] : List Nat)).heap ∧
    (lheap_list2 ([4, 1, 3, 2] : List Nat)).ltree :=
  ⟨heap_lheap_list2 _, ltree_lheap_list2 _⟩
example : (lheap_list2 ([2, 1, 1, 2] : List Nat)).heap ∧
    (lheap_list2 ([2, 1, 1, 2] : List Nat)).ltree :=
  ⟨heap_lheap_list2 _, ltree_lheap_list2 _⟩

-- Incorrect stored ranks and right-heavy nodes are not leftist trees.
example : ¬ ltree (N 0 (1 : Nat) E E) := by simp [ltree, rank]
example : ¬ ltree (N 2 (1 : Nat) E (LHeap.singleton 2)) := by
  simp [ltree, rank, LHeap.singleton]
example : ¬ heap (N 1 (3 : Nat) (LHeap.singleton 1) E) := by
  simp [heap, all_le, LHeap.singleton]

example : T_merge (E : LHeap Nat) (LHeap.singleton 7) = 0 := by rfl
example : T_merge (LHeap.singleton (7 : Nat)) E = 0 := by rfl
example : T_merge (LHeap.singleton (3 : Nat)) (LHeap.singleton 1) = 1 := by rfl
example : T_merge (merge_all2 odd) (LHeap.singleton 4) = 2 := by
  rw [oddResult]
  rfl
example : T_merge_adj2 accumulator [] = 0 := by simp [T_merge_adj2]
example : T_merge_adj2 accumulator [LHeap.singleton 7] = 0 := by
  simp [T_merge_adj2]
example : T_merge_adj2 accumulator odd = 1 := by
  rw [T_merge_adj2_eq]
  rfl
example : T_merge_adj2 accumulator even = 2 := by
  rw [T_merge_adj2_eq]
  rfl
example : T_merge_adj2 accumulator duplicates = 2 := by
  rw [T_merge_adj2_eq]
  rfl
example : T_merge_adj2 accumulator odd = T_merge_adj odd := T_merge_adj2_eq _ _
example : T_merge_adj2 accumulator even = T_merge_adj even := T_merge_adj2_eq _ _
example : T_merge_adj2 accumulator duplicates = T_merge_adj duplicates :=
  T_merge_adj2_eq _ _

end Cslib.Algorithms.Lean.LeftistHeapTests
