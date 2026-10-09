/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Quick
import Mathlib.Data.Nat.Basic

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

example : (partition3 5 [7, 2, 5, 9, 1, 5, 8, 3]).ret =
    { below := [2, 1, 3], equal := [5, 5], above := [7, 9, 8] } := by
  decide

example (pivot : Nat) (xs : List Nat) :
    (partition3 pivot xs).ret.below = xs.filter (fun x => x < pivot) :=
  partition3_below_eq_filter pivot xs

example : (partition3 2 ([] : List Nat)).ret =
    { below := [], equal := [], above := [] } := by
  decide

example : (partition3 2 ([] : List Nat)).time = 0 := by
  decide

example : (partition3 7 [7]).ret =
    { below := [], equal := [7], above := [] } := by
  decide

example : (partition3 2 [2, 2, 2]).ret =
    { below := [], equal := [2, 2, 2], above := [] } := by
  decide

example : (partition3 2 [3, 2, 1, 2, 1]).ret =
    { below := [1, 1], equal := [2, 2], above := [3] } := by
  decide

example : (partition3 2 [3, 2, 1, 2, 1]).time = 5 := by
  decide

example : (quickSort ([] : List Nat)).ret = [] := by
  decide

example : (quickSort ([] : List Nat)).time = 0 := by
  decide

example : (quickSort [7]).ret = [7] := by
  decide

example : (quickSort [7]).time = 0 := by
  decide

example : (quickSort [1, 2, 3, 4]).ret = [1, 2, 3, 4] := by
  decide

example : (quickSort [1, 2, 3, 4]).time = 6 := by
  decide

example : (quickSort [4, 3, 2, 1]).ret = [1, 2, 3, 4] := by
  decide

example : (quickSort [4, 3, 2, 1]).time = 6 := by
  decide

example : (quickSort [2, 1, 2, 1]).ret = [1, 1, 2, 2] := by
  decide

example : (quickSort [2, 1, 2, 1]).time = 4 := by
  decide

example : (quickSort [5, 5, 5, 5]).ret = [5, 5, 5, 5] := by
  decide

example : (quickSort [5, 5, 5, 5]).time = 3 := by
  decide

example (pivot : Nat) (xs : List Nat) :
    List.Perm
        ((partition3 pivot xs).ret.below ++
          (partition3 pivot xs).ret.equal ++
          (partition3 pivot xs).ret.above)
        xs :=
  (partition3_correct pivot xs).1

example (pivot : Nat) (xs : List Nat) :
    (partition3 pivot xs).ret.equal = xs.filter (fun x => x = pivot) :=
  partition3_equal_eq_filter pivot xs

example (pivot : Nat) (xs : List Nat) :
    (partition3 pivot xs).ret.above = xs.filter (fun x => pivot < x) :=
  partition3_above_eq_filter pivot xs

example (pivot : Nat) (xs : List Nat) :
    (partition3 pivot xs).ret.below.length +
        (partition3 pivot xs).ret.equal.length +
        (partition3 pivot xs).ret.above.length = xs.length :=
  partition3_length pivot xs

example (xs : List Nat) :
    List.Pairwise (fun x y => x ≤ y) (quickSort xs).ret ∧
      List.Perm (quickSort xs).ret xs :=
  quickSort_correct xs

example (xs : List Nat) :
    (quickSort xs).time ≤ xs.length * (xs.length - 1) / 2 :=
  quickSort_time xs

universe u

example {α : Type u} [LinearOrder α] (pivot : α) (xs : List α) :
    ThreeWayPartition α :=
  (partition3 pivot xs).ret

example {α : Type u} [LinearOrder α] (xs : List α) :
    List.Perm (quickSort xs).ret xs :=
  (quickSort_correct xs).2

end Cslib.Algorithms.Lean.TimeM
