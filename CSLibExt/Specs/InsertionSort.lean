/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Specs.Sorting
public import CSLibExt.Algorithms.Lean.Sort.InsertionCost

/-!
# Insertion sort satisfies the sorting contract

The executable algorithms and their correctness proofs come from Mathlib
and `Cslib.Algorithms.Lean.TimeM`. No insertion algorithm is defined here.
`sorting_insertionSort` connects the canonical costed result's `ret` field
to `SortingSpec`; it does not assert a machine-cost model.

`insert` and `isort` retain the old call syntax as definitional compatibility
shims for Mathlib's `List.orderedInsert` and `List.insertionSort` under `≤`.
`sorting_isort` retains the corresponding correctness entry point. For
membership, permutation, and insertion sortedness, use Mathlib's
`List.mem_orderedInsert`, `List.perm_orderedInsert`, and
`List.Pairwise.orderedInsert` directly.
-/

@[expose] public section

universe u

namespace CSLibExt.Specs.Sorting

variable {α : Type u} [LinearOrder α]

/-- Compatibility name for Mathlib's ordered insertion under `≤`. -/
abbrev insert (x : α) (xs : List α) : List α :=
  List.orderedInsert (· ≤ ·) x xs

/-- Compatibility name for Mathlib's insertion sort under `≤`. -/
abbrev isort (xs : List α) : List α := List.insertionSort (· ≤ ·) xs

/-- Mathlib's insertion sort satisfies the generic sorting contract. -/
theorem sorting_isort (xs : List α) : SortingSpec xs (isort xs) :=
  ⟨List.perm_insertionSort (· ≤ ·) xs,
    List.pairwise_insertionSort (· ≤ ·) xs⟩

/-- The canonical costed insertion sort satisfies the same return contract. -/
theorem sorting_insertionSort (xs : List α) :
    SortingSpec xs
      (Cslib.Algorithms.Lean.TimeM.insertionSort xs).ret := by
  exact (Cslib.Algorithms.Lean.TimeM.insertionSort_correct xs).symm

end CSLibExt.Specs.Sorting
