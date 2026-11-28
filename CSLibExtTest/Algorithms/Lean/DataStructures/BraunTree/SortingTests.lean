/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Sorting

/-!
# Sorting regression tests

Concrete computations for the two sorting algorithms
(`BraunTree.Sorting`): `heapOfA` / `listOfA` via `merge`,
`heapify` / `heapOfB` / `listOfB'` via `delMin`, and the AFP's
`shuffle100` test input (sortedness and multiset via the general
theorems, since the well-founded-recursive functions do not
reduce in the kernel).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BraunTree.SortingTests

open BraunTree
open BraunTree.Sorting

/-- Algorithm A sorts `[3, 1, 2]`. -/
example : listOfA (heapOfA [3, 1, 2]) = [1, 2, 3] := by
  simp [listOfA, heapOfA, insert, merge]

/-- Algorithm B sorts `[3, 1, 2]` (via `sorted_listOfB`). -/
example : (listOfB' (heapOfA [3, 1, 2])).Pairwise (· ≤ ·) :=
  sorted_listOfB _ (braun_heapOfA _) (heap_heapOfA _)

/-- Algorithm B preserves the multiset of `[3, 1, 2]` (via `mset_listOfB`). -/
example : ((listOfB' (heapOfA [3, 1, 2]) : List Nat) : Multiset Nat) =
    ([3, 1, 2] : Multiset Nat) := by
  rw [mset_listOfB _ (braun_heapOfA _), mset_heapOfA]

/-- `heapify` on `[5, 1, 4, 2]` with `n = 3` leaves `[2]`. -/
example : (heapify 3 [5, 1, 4, 2]).2 = [2] :=
  heapify_snd 3 _ (by decide)

/-- The `heapify` heap has the first three elements. -/
example : msetTree (heapify 3 [5, 1, 4, 2]).1 = ({1, 5, 4} : Multiset ℕ) := by
  simp [heapify, siftDown, msetTree]

/-- Sorting's `merge` on two singletons (the AFP `value` example). -/
example : merge (BraunTree.Node BraunTree.Leaf 0 BraunTree.Leaf)
    (BraunTree.Node BraunTree.Leaf 0 BraunTree.Leaf) =
    BraunTree.Node BraunTree.Leaf 0
      (BraunTree.Node BraunTree.Leaf 0 BraunTree.Leaf) := by
  simp [merge]

/-- `merge` with the empty tree. -/
example : merge (BraunTree.Leaf : BraunTree ℕ)
    (BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf) =
    BraunTree.Node BraunTree.Leaf 2 BraunTree.Leaf := by
  simp [merge]

/-- The AFP's `shuffle100` test input: a permutation of `0..99`. -/
def shuffle100 : List Nat :=
  [50, 7, 77, 15, 42, 82, 87, 68, 69, 29, 43, 24, 84, 12, 35, 30, 95, 45, 14, 47,
   54, 66, 96, 71, 98, 4, 22, 0, 92, 86, 34, 33, 57, 91, 20, 13, 64, 73, 70, 8,
   85, 40, 16, 18, 81, 99, 63, 41, 56, 72, 79, 48, 78, 52, 25, 49, 65, 90, 26, 76,
   3, 59, 74, 58, 46, 38, 61, 94, 75, 11, 88, 31, 53, 17, 44, 89, 39, 93, 62, 5,
   1, 21, 6, 55, 83, 28, 37, 60, 19, 67, 23, 97, 51, 10, 27, 32, 2, 36, 9, 80]

/-- Algorithm A sorts `shuffle100` (via `sorted_listOfA`). -/
example : (listOfA (heapOfA shuffle100)).Pairwise (· ≤ ·) :=
  sorted_listOfA _ (heap_heapOfA _)

/-- Algorithm A preserves the multiset of `shuffle100` (via `msetA`). -/
example : ((listOfA (heapOfA shuffle100) : List Nat) : Multiset Nat) =
    (shuffle100 : Multiset Nat) :=
  msetA shuffle100

/-- Algorithm B sorts `shuffle100` (via `sorted_listOfB`). -/
example : (listOfB' (heapOfB shuffle100)).Pairwise (· ≤ ·) :=
  sorted_listOfB _ (braun_heapify (le_refl _)) (heap_heapify (le_refl _))

/-- Algorithm B preserves the multiset of `shuffle100` (via `msetB`). -/
example : ((listOfB' (heapOfB shuffle100) : List Nat) : Multiset Nat) =
    (shuffle100 : Multiset Nat) :=
  msetB shuffle100

end Cslib.Algorithms.Lean.BraunTree.SortingTests
