/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Ordered insertion into a list

`orderedInsert x xs` inserts `x` into `xs` at its sorted position. On a
strictly sorted list (`xs.Pairwise (· < ·)`) this returns `xs` unchanged
when `x` is already present (`orderedInsert_eq_of_mem`); on an arbitrary
list the scan stops at the first element not smaller than `x`, so a
duplicate occurring later is not detected — for example
`orderedInsert 2 [3, 2] = [2, 3, 2]`. The tree implementations in this
library (2-3 trees and B-trees) only apply it to strictly sorted
flattenings, whose flattening lemmas state that tree insertion acts on
the inorder flattening by `orderedInsert`.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

variable {α : Type u}

/-- Insert a key into a list at its sorted position: the scan stops at the
first element that is not smaller than the key and stops there, so a key
already present is ignored only when the list is strictly sorted (see
`orderedInsert_eq_of_mem`); on an unsorted list a later duplicate is not
detected. This is the list-level specification of tree insertion. -/
public def orderedInsert [LinearOrder α] (x : α) : List α → List α
  | [] => [x]
  | a :: as =>
      if x < a then x :: a :: as
      else if a < x then a :: orderedInsert x as
      else a :: as

/-- Ordered insertion into a list adds exactly the inserted key. -/
public theorem mem_orderedInsert [LinearOrder α] {x y : α} {xs : List α} :
    y ∈ orderedInsert x xs ↔ y = x ∨ y ∈ xs := by
  induction xs with
  | nil => simp [orderedInsert]
  | cons a as ih =>
    by_cases hxa : x < a
    · simp [orderedInsert, hxa]
    · by_cases hax : a < x
      · simp [orderedInsert, hxa, hax, ih, or_left_comm]
      · have hEq : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        subst hEq
        simp [orderedInsert, hxa]

/-- On a strictly sorted list, inserting an already-present key is a no-op.
This is the duplicate-elision contract the tree implementations rely on;
without strict sortedness it fails, e.g. `orderedInsert 2 [3, 2] = [2, 3, 2]`. -/
public theorem orderedInsert_eq_of_mem [LinearOrder α] {x : α} {xs : List α}
    (hSorted : xs.Pairwise (· < ·)) (hMem : x ∈ xs) :
    orderedInsert x xs = xs := by
  induction xs with
  | nil => simp at hMem
  | cons a as ih =>
      rw [List.pairwise_cons] at hSorted
      cases hMem with
      | head =>
          have hxx : ¬ x < x := lt_irrefl x
          simp [orderedInsert, hxx]
      | tail _ hMemAs =>
          have hax : a < x := hSorted.1 x hMemAs
          simp [orderedInsert, hax, not_lt.mpr (le_of_lt hax),
            ih hSorted.2 hMemAs]

end Cslib.Algorithms.Lean
