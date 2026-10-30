/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LeftistHeap

/-!
# Leftist-heap public proof-interface tests

Clients of the imported `auto-fdsa-15-04/environment/Task.lean` and
`auto-fdsa-15-04/solution/Solution.lean`, pinned at
`16412d086eb5af2e74da78731bde50da0667bc79`, can use all four original
conjuncts, both full-merge variants, and nonempty accumulator semantics.
No total-runtime claim is inferred from the merge-step cost equality.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LeftistHeapAPITests

open LHeap

-- `singleton` and its structural properties do not require an order on the carrier.
inductive Unordered where
| left
| right

example (xs : List Unordered) :
    sumMSet (xs.map singleton) = (xs : Multiset Unordered) ∧
    LTreeList (xs.map singleton) :=
  ⟨sumMSet_map_singleton xs, ltreeList_map_singleton xs⟩

variable {α : Type} [LinearOrder α]

-- Check the complete frozen graded statement, not merely selected projections.
example :
    (∀ xs : List α, (lheap_list2 xs).mset_tree = (xs : Multiset α)) ∧
    (∀ xs : List α, (lheap_list2 xs).heap) ∧
    (∀ xs : List α, (lheap_list2 xs).ltree) ∧
    (∀ (acc ts : List (LHeap α)),
      T_merge_adj2 acc ts = T_merge_adj ts) := fdsa_chap15_ex04

example (xs : List α) :
    (lheap_list2 xs).mset_tree = (xs : Multiset α) ∧
    (lheap_list2 xs).heap ∧ (lheap_list2 xs).ltree :=
  lheap_list2_correct xs

example (left right : LHeap α) :
    (left.merge right).mset_tree = left.mset_tree + right.mset_tree :=
  mset_merge left right
example (left right : LHeap α) (hl : left.heap) (hr : right.heap) :
    (left.merge right).heap := heap_merge left right hl hr
example (left right : LHeap α) (hl : left.ltree) (hr : right.ltree) :
    (left.merge right).ltree := ltree_merge left right hl hr

example (acc ts : List (LHeap α)) :
    merge_adj2 acc ts = acc.reverse ++ merge_adj ts :=
  merge_adj2_eq_reverse_append acc ts
example (acc ts : List (LHeap α)) :
    sumMSet (merge_adj2 acc ts) = sumMSet acc + sumMSet ts :=
  sumMSet_merge_adj2 acc ts
example (acc ts : List (LHeap α))
    (ha : HeapList acc) (ht : HeapList ts) :
    HeapList (merge_adj2 acc ts) := heapList_merge_adj2 acc ts ha ht
example (acc ts : List (LHeap α))
    (ha : LTreeList acc) (ht : LTreeList ts) :
    LTreeList (merge_adj2 acc ts) := ltreeList_merge_adj2 acc ts ha ht
example (acc ts : List (LHeap α)) :
    T_merge_adj2 acc ts = T_merge_adj ts := T_merge_adj2_eq acc ts

example (ts : List (LHeap α)) :
    (merge_all ts).mset_tree = sumMSet ts := mset_merge_all ts
example (ts : List (LHeap α)) :
    (merge_all2 ts).mset_tree = sumMSet ts := mset_merge_all2 ts
example (ts : List (LHeap α)) (ht : HeapList ts) :
    (merge_all ts).heap ∧ (merge_all2 ts).heap :=
  ⟨heap_merge_all ts ht, heap_merge_all2 ts ht⟩
example (ts : List (LHeap α)) (ht : LTreeList ts) :
    (merge_all ts).ltree ∧ (merge_all2 ts).ltree :=
  ⟨ltree_merge_all ts ht, ltree_merge_all2 ts ht⟩

-- A real nonempty accumulator is included in content and invariant checks.
example (x y : α) (xs : List α) :
    sumMSet (merge_adj2 [singleton x, singleton y] (xs.map singleton)) =
      ({x} : Multiset α) + {y} + (xs : Multiset α) := by
  rw [sumMSet_merge_adj2, sumMSet_map_singleton]
  simp [sumMSet, mset_singleton]

example (x y : α) (xs : List α) :
    HeapList (merge_adj2 [singleton x, singleton y] (xs.map singleton)) ∧
    LTreeList (merge_adj2 [singleton x, singleton y] (xs.map singleton)) := by
  have ha : HeapList [singleton x, singleton y] := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact heap_singleton x
    · exact heap_singleton y
  have la : LTreeList [singleton x, singleton y] := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ltree_singleton x
    · exact ltree_singleton y
  exact ⟨heapList_merge_adj2 _ _ ha (heapList_map_singleton xs),
    ltreeList_merge_adj2 _ _ la (ltreeList_map_singleton xs)⟩

example (x y : α) (xs : List α) :
    T_merge_adj2 [singleton x, singleton y] (xs.map singleton) =
      T_merge_adj (xs.map singleton) := T_merge_adj2_eq _ _

end Cslib.Algorithms.Lean.LeftistHeapAPITests
