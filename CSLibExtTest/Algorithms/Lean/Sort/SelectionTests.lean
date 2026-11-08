/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Selection
import Mathlib.Data.Nat.Basic

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

example : (extractMin 4 [3, 1, 2, 1]).ret = (1, [4, 3, 2, 1]) := by
  decide

example : (extractMin 4 [3, 1, 2, 1]).time = 4 := by
  decide

example : (selectionSort ([] : List Nat)).ret = [] := by
  decide

example : (selectionSort ([] : List Nat)).time = 0 := by
  decide

example : (selectionSort [7]).ret = [7] := by
  decide

example : (selectionSort [7]).time = 0 := by
  decide

example : (selectionSort [1, 2, 3, 4]).ret = [1, 2, 3, 4] := by
  decide

example : (selectionSort [1, 2, 3, 4]).time = 6 := by
  decide

example : (selectionSort [4, 3, 2, 1]).ret = [1, 2, 3, 4] := by
  decide

example : (selectionSort [4, 3, 2, 1]).time = 6 := by
  decide

example : (selectionSort [2, 1, 2, 1]).ret = [1, 1, 2, 2] := by
  decide

example : (selectionSort [2, 1, 2, 1]).time = 6 := by
  decide

example (xs : List Nat) :
    List.Pairwise (fun x y => x ≤ y) (selectionSort xs).ret ∧
      List.Perm (selectionSort xs).ret xs :=
  selectionSort_correct xs

example (xs : List Nat) :
    (selectionSort xs).time = xs.length * (xs.length - 1) / 2 :=
  selectionSort_time xs

universe u

example {α : Type u} [LinearOrder α] (xs : List α) :
    List.Perm (selectionSort xs).ret xs :=
  (selectionSort_correct xs).2

end Cslib.Algorithms.Lean.TimeM
