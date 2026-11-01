/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

@[expose] public section

namespace CSLibExt.Specs.Sorting

/-!
# Sorting spec (Week 2 skeleton, 90-day plan #2 SPECS)

The canonical relational sorting spec, written with core-Lean definitions
so this skeleton compiles standalone under Lean v4.35.0. In Atlas,
`SortedProp` below aliases Mathlib's `List.Sorted`
(`List.Pairwise (· ≤ ·)`), and `List.Perm` is Mathlib's. This file does
NOT define a new `Sorted` or `Perm`.

CPythonListsort's comparator-parameterized `Sorted` over `Array` is a
*different* spec, bridged, never silently aliased.

Positive witness: `[1, 2]`; negative witness: `[2, 1]` is a permutation
of `[1, 2]` but not sorted.
-/

/-- Sortedness as pairwise `≤`. In Atlas this aliases `List.Sorted`. -/
def SortedProp (xs : List Nat) : Prop := List.Pairwise (· ≤ ·) xs

/-- A list `ys` is a sorted permutation of `xs` iff it is a permutation
of `xs` and sorted under `≤`. Relational spec: no algorithm mentioned. -/
def SortingSpec (xs ys : List Nat) : Prop :=
  List.Perm ys xs ∧ SortedProp ys

/-- Positive witness: `[1, 2]` satisfies the spec for `[2, 1]`. -/
example : SortingSpec [2, 1] [1, 2] := by
  refine ⟨?_, ?_⟩
  · exact List.Perm.swap 2 1 []
  · exact List.Pairwise.cons (by simp)
      (List.Pairwise.cons (by simp) List.Pairwise.nil)

/-- Negative witness: `[2, 1]` is not sorted. -/
example : ¬ SortedProp ([2, 1] : List Nat) := by
  intro h
  cases h with
  | cons h1 _ => simp at h1

/-- The empty list satisfies the spec for itself. -/
example : SortingSpec [] [] :=
  ⟨List.Perm.refl _, List.Pairwise.nil⟩

end CSLibExt.Specs.Sorting
