/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Heap

/-!
# Tests for heap sort

These importing-client examples exercise the executable boundary cases and public correctness API.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

private theorem heapSort_eq_of_pairwise_of_perm (xs expected : List Nat)
    (hsorted : List.Pairwise (fun x y => x ≤ y) expected)
    (hperm : expected.Perm xs) : heapSort xs = expected :=
  ((heapSort_perm xs).trans hperm.symm).eq_of_pairwise
    (fun _ _ _ _ hab hba => le_antisymm hab hba) (heapSort_sorted xs) hsorted

example : heapSort ([] : List Nat) = [] := by
  apply heapSort_eq_of_pairwise_of_perm <;> decide

example : heapSort [7] = [7] := by
  apply heapSort_eq_of_pairwise_of_perm <;> decide

example : heapSort [3, 1, 3, 2, 1] = [1, 1, 2, 3, 3] := by
  apply heapSort_eq_of_pairwise_of_perm <;> decide

example : heapSort [5, 4, 3, 2, 1] = [1, 2, 3, 4, 5] := by
  apply heapSort_eq_of_pairwise_of_perm <;> decide

example : heapSort [8, 3, 6, 1, 7, 2, 5, 4] = [1, 2, 3, 4, 5, 6, 7, 8] := by
  apply heapSort_eq_of_pairwise_of_perm <;> decide

example {α : Type} [LinearOrder α] (xs : List α) :
    List.Perm (heapSort xs) xs :=
  heapSort_perm xs

example {α : Type} [LinearOrder α] (xs : List α) :
    (↑(heapSort xs) : Multiset α) = xs :=
  heapSort_multiset xs

example {α : Type} [LinearOrder α] (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (heapSort xs) :=
  heapSort_sorted xs

example {α : Type} [LinearOrder α] (xs : List α) :
    List.Pairwise (fun x y => x ≤ y) (heapSort xs) ∧
      List.Perm (heapSort xs) xs :=
  heapSort_correct xs

end Cslib.Algorithms.Lean
