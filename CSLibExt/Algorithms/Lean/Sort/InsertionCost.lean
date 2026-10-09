/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.Sort.Insertion
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Choose.Basic

/-!
# Comparison cost of insertion sort

This module specializes CSLib's `List.insertionSortM` to `TimeM Nat`. Exactly one unit is charged
for each order comparison; pattern matching, recursive calls, and pure list construction are free.

The return-value proof reuses CSLib's `Cslib.IsMonadHom.map_listInsertionSortM`. Sortedness and
permutation reuse Mathlib's `List.pairwise_insertionSort` and `List.perm_insertionSort`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type} [LinearOrder α]

/-- Decides `x ≤ y`, charging one unit for the comparison. -/
abbrev compareLE (x y : α) : TimeM Nat Bool := do
  ✓ return decide (x ≤ y)

/-- Insertion sort with one unit of time charged for every order comparison. -/
abbrev insertionSort (xs : List α) : TimeM Nat (List α) :=
  List.insertionSortM compareLE xs

/-- Erasing comparison costs recovers Mathlib's insertion sort. -/
@[simp]
theorem ret_insertionSort (xs : List α) :
    (insertionSort xs).ret = List.insertionSort (fun x y => x ≤ y) xs := by
  simpa [insertionSort] using
    Id.ext_iff.mp
      (isMonadHom_pure_ret.map_listInsertionSortM compareLE xs)

/-- Insertion sort returns a nondecreasing list. -/
theorem insertionSort_sorted (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (insertionSort xs).ret := by
  simpa using List.pairwise_insertionSort (fun x y : α => x ≤ y) xs

/-- Insertion sort preserves every input occurrence, including duplicates. -/
theorem insertionSort_perm (xs : List α) : List.Perm (insertionSort xs).ret xs := by
  simpa using List.perm_insertionSort (fun x y : α => x ≤ y) xs

/-- Insertion sort returns a sorted permutation of its input. -/
theorem insertionSort_correct (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (insertionSort xs).ret ∧
      List.Perm (insertionSort xs).ret xs :=
  ⟨insertionSort_sorted xs, insertionSort_perm xs⟩

private theorem orderedInsert_time_le (a : α) (xs : List α) :
    (List.orderedInsertM compareLE a xs).time ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      by_cases h : a ≤ b
      · simp [List.orderedInsertM_cons, h, compareLE, TimeM.tick]
      · simp [List.orderedInsertM_cons, h, compareLE]
        omega

private theorem insertionSort_time_le_choose (xs : List α) :
    (insertionSort xs).time ≤ xs.length.choose 2 := by
  induction xs with
  | nil => simp [insertionSort]
  | cons a xs ih =>
      have hInsert :
          (List.orderedInsertM compareLE a (insertionSort xs).ret).time ≤ xs.length := by
        calc
          (List.orderedInsertM compareLE a (insertionSort xs).ret).time ≤
              (insertionSort xs).ret.length := orderedInsert_time_le a (insertionSort xs).ret
          _ = xs.length := (insertionSort_perm xs).length_eq
      simp only [insertionSort, List.insertionSortM_cons, time_bind, List.length_cons]
      calc
        (List.insertionSortM compareLE xs).time +
              (List.orderedInsertM compareLE a (List.insertionSortM compareLE xs).ret).time ≤
            xs.length.choose 2 + xs.length := Nat.add_le_add ih hInsert
        _ = (xs.length + 1).choose 2 := by
          simpa [Nat.choose_one_right, Nat.add_comm, Nat.succ_eq_add_one] using
            (Nat.choose_succ_succ xs.length 1).symm

/-- Insertion sort performs at most `n * (n - 1) / 2` comparisons on a list of length `n`. -/
theorem insertionSort_time (xs : List α) :
    (insertionSort xs).time ≤ xs.length * (xs.length - 1) / 2 := by
  rw [← Nat.choose_two_right]
  exact insertionSort_time_le_choose xs

end Cslib.Algorithms.Lean.TimeM
