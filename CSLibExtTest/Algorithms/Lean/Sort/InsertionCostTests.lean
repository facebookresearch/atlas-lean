/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.InsertionCost

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

example : (insertionSort ([] : List Nat)).ret = [] := by simp [insertionSort]
example : (insertionSort ([] : List Nat)).time = 0 := by simp [insertionSort]

example : (insertionSort [7]).ret = [7] := by simp [insertionSort]
example : (insertionSort [7]).time = 0 := by simp [insertionSort]

example : (insertionSort [1, 2, 3, 4]).ret = [1, 2, 3, 4] := by
  simp [insertionSort, compareLE]
example : (insertionSort [1, 2, 3, 4]).time = 3 := by simp [insertionSort, compareLE]

example : (insertionSort [4, 3, 2, 1]).ret = [1, 2, 3, 4] := by
  simp [insertionSort, compareLE]
example : (insertionSort [4, 3, 2, 1]).time = 6 := by simp [insertionSort, compareLE]

example : (insertionSort [2, 1, 2, 1]).ret = [1, 1, 2, 2] := by
  simp [insertionSort, compareLE]
example : (insertionSort [2, 1, 2, 1]).time = 5 := by simp [insertionSort, compareLE]

example (xs : List Nat) :
    List.Pairwise (fun x y => x ≤ y) (insertionSort xs).ret ∧
      List.Perm (insertionSort xs).ret xs :=
  insertionSort_correct xs

example (xs : List Nat) :
    (insertionSort xs).time ≤ xs.length * (xs.length - 1) / 2 :=
  insertionSort_time xs

end Cslib.Algorithms.Lean.TimeM
