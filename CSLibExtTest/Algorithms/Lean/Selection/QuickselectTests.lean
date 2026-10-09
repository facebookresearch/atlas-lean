/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Selection.Quickselect
import Mathlib.Data.Nat.Basic

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

example : (quickselect ([] : List Nat) 0).ret = none := by
  decide

example : (quickselect [7] 0).ret = some 7 := by
  decide

example : (quickselect [7] 0).time = 0 := by
  decide

example : (quickselect [7] 1).ret = none := by
  decide

example : (quickselect [7] 7).ret = none := by
  decide

example : (quickselect [5, 5, 5] 0).ret = some 5 := by
  decide

example : (quickselect [5, 5, 5] 1).ret = some 5 := by
  decide

example : (quickselect [5, 5, 5] 2).ret = some 5 := by
  decide

example : (quickselect [5, 5, 5] 2).time = 2 := by
  decide

example : (quickselect [5, 5, 5] 3).ret = none := by
  decide

example : (quickselect [5, 5, 5] 3).time = 0 := by
  decide

example : (quickselect [3, 1, 2, 2, 2, 4] 0).ret = some 1 := by
  decide

example : (quickselect [3, 1, 2, 2, 2, 4] 1).ret = some 2 := by
  decide

example : (quickselect [3, 1, 2, 2, 2, 4] 3).ret = some 2 := by
  decide

example : (quickselect [3, 1, 2, 2, 2, 4] 5).ret = some 4 := by
  decide

example : (quickselect [1, 2, 3, 4] 2).ret = some 3 := by
  decide

example : (quickselect [4, 3, 2, 1] 2).ret = some 3 := by
  decide

example : (quickselect [2, 1, 2, 1] 2).ret = some 2 := by
  decide

example : (quickselect [3, 1, 2] 3).ret = none := by
  decide

example : (quickselect [3, 1, 2] 8).ret = none := by
  decide

example {xs : List Nat} {k : Nat} {x : Nat}
    (h : (quickselect xs k).ret = some x) :
    x ∈ xs ∧
      xs.countP (fun y => decide (y < x)) ≤ k ∧
      k < xs.countP (fun y => decide (y ≤ x)) :=
  quickselect_correct h

example (xs : List Nat) (k : Nat) :
    (quickselect xs k).ret = none ↔ xs.length ≤ k :=
  quickselect_eq_none_iff xs k

example (xs : List Nat) (k : Nat) :
    (quickselect xs k).ret = (xs.insertionSort (· ≤ ·))[k]? :=
  quickselect_eq_getElem?_insertionSort xs k

example : (quickselect [3, 1, 2, 2, 2, 4] 0).ret = some 1 := by
  rw [quickselect_eq_getElem?_insertionSort]
  simp

example : (quickselect [3, 1, 2, 2, 2, 4] 2).ret = some 2 := by
  rw [quickselect_eq_getElem?_insertionSort]
  simp

example : (quickselect [3, 1, 2, 2, 2, 4] 5).ret = some 4 := by
  rw [quickselect_eq_getElem?_insertionSort]
  simp

example : (quickselect [5, 5, 5] 1).ret = some 5 := by
  rw [quickselect_eq_getElem?_insertionSort]
  simp

example : (quickselect [3, 1, 2, 2, 2, 4] 6).ret = none := by
  rw [quickselect_eq_getElem?_insertionSort]
  simp

example : (quickselect ([] : List Nat) 0).ret = none := by
  rw [quickselect_eq_getElem?_insertionSort]
  simp

example : (quickselect [1, 2, 3, 4] 3).time = 6 := by
  decide

example : (quickselect [4, 3, 2, 1] 0).time = 6 := by
  decide

example (xs : List Nat) (k : Nat) :
    (quickselect xs k).time ≤ xs.length * (xs.length - 1) / 2 :=
  quickselect_time xs k

universe u

example {α : Type u} [LinearOrder α] (xs : List α) (k : Nat) :
    (quickselect xs k).ret = none ↔ xs.length ≤ k :=
  quickselect_eq_none_iff xs k

end Cslib.Algorithms.Lean.TimeM
