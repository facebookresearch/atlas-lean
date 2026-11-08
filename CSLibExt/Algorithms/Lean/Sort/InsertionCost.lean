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

This module specializes CSLib's insertion-sort procedure to `TimeM Nat`. The explicit
`TimeM.bind` calls allow Boolean comparisons in `Type 0` and list results in any universe;
the canonical generic-monad API is restricted to `Type 0`. Equality with that API is proved
where it applies. Exactly one unit is charged for each order comparison; pattern matching,
recursive calls, and pure list construction are free. Sortedness and permutation reuse
Mathlib's `List.pairwise_insertionSort` and `List.perm_insertionSort`.
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.TimeM

variable {α : Type u} [LinearOrder α]

/-- Decides `x ≤ y`, charging one unit for the comparison. -/
abbrev compareLE (x y : α) : TimeM Nat Bool := do
  ✓ return decide (x ≤ y)

/-- Insert one element, allowing comparison and output values in different universes. -/
def insertionSortInsert (a : α) : List α → TimeM Nat (List α)
  | [] => pure [a]
  | b :: xs => TimeM.bind (compareLE a b) fun before =>
      if before then pure (a :: b :: xs)
      else TimeM.bind (insertionSortInsert a xs) fun tail => pure (b :: tail)

/-- Insertion sort with one unit of time charged for every order comparison. -/
def insertionSort : List α → TimeM Nat (List α)
  | [] => pure []
  | a :: xs => TimeM.bind (insertionSort xs) (insertionSortInsert a)

/-- Inserting one element returns Mathlib's ordered insert of that element. -/
theorem ret_insertionSortInsert (a : α) (xs : List α) :
    (insertionSortInsert a xs).ret = List.orderedInsert (fun x y => x ≤ y) a xs := by
  induction xs with
  | nil => simp [insertionSortInsert]
  | cons b xs ih =>
      by_cases h : a ≤ b <;>
        simp [insertionSortInsert, compareLE, TimeM.bind, List.orderedInsert_cons, h, ih]

/-- Erasing comparison costs recovers Mathlib's insertion sort. -/
@[simp]
theorem ret_insertionSort (xs : List α) :
    (insertionSort xs).ret = List.insertionSort (fun x y => x ≤ y) xs := by
  induction xs with
  | nil => simp [insertionSort]
  | cons a xs ih =>
      simpa only [insertionSort, TimeM.bind, ret_insertionSortInsert,
        List.insertionSort_cons, ih]

private theorem insertionSortInsert_eq_orderedInsertM {β : Type} [LinearOrder β]
    (a : β) (xs : List β) :
    insertionSortInsert a xs = List.orderedInsertM compareLE a xs := by
  induction xs with
  | nil => simp [insertionSortInsert]
  | cons b xs ih =>
      apply TimeM.ext <;> by_cases h : a ≤ b <;>
        simp [insertionSortInsert, List.orderedInsertM_cons, compareLE, TimeM.bind, h, ih]

/-- On `Type 0`, the complete return value and comparison charges equal CSLib's API. -/
@[simp]
theorem insertionSort_eq_insertionSortM {β : Type} [LinearOrder β] (xs : List β) :
    insertionSort xs = List.insertionSortM compareLE xs := by
  induction xs with
  | nil => simp [insertionSort]
  | cons a xs ih =>
      apply TimeM.ext <;>
        simp [insertionSort, List.insertionSortM_cons, TimeM.bind, ih,
          insertionSortInsert_eq_orderedInsertM]

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

/-- Inserting one element charges at most one comparison per existing element. -/
theorem insertionSortInsert_time_le (a : α) (xs : List α) :
    (insertionSortInsert a xs).time ≤ xs.length := by
  induction xs with
  | nil => simp [insertionSortInsert]
  | cons b xs ih =>
      by_cases h : a ≤ b
      · simp [insertionSortInsert, h, compareLE, TimeM.tick, TimeM.bind]
      · simp [insertionSortInsert, h, compareLE, TimeM.bind]
        omega

private theorem insertionSort_time_le_choose (xs : List α) :
    (insertionSort xs).time ≤ xs.length.choose 2 := by
  induction xs with
  | nil => simp [insertionSort]
  | cons a xs ih =>
      have hInsert :
          (insertionSortInsert a (insertionSort xs).ret).time ≤ xs.length := by
        calc
          (insertionSortInsert a (insertionSort xs).ret).time ≤
              (insertionSort xs).ret.length := insertionSortInsert_time_le a (insertionSort xs).ret
          _ = xs.length := (insertionSort_perm xs).length_eq
      simp only [insertionSort, TimeM.bind, List.length_cons]
      calc
        (insertionSort xs).time +
              (insertionSortInsert a (insertionSort xs).ret).time ≤
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
