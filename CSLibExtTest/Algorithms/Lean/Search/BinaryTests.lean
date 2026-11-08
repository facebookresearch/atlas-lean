/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Search.Binary
import Mathlib.Algebra.Order.Ring.Nat
import all Init.Data.Array.BinSearch

@[expose] public section

/-!
# Binary search tests

These examples exercise the inclusive search bounds, clamping of an oversized
upper bound, duplicate keys, and empty or invalid search regions.
-/

namespace Cslib.Algorithms.Lean.BinaryTests

open Cslib.Algorithms.Lean

private abbrev natLt (a b : Nat) : Bool := decide (a < b)

example : (#[] : Array Nat).binSearch 2 natLt = none := by decide

example : (#[2] : Array Nat).binSearch 2 natLt = some 2 := by
  simp [Array.binSearch, Array.binSearchAux, natLt]

example : (#[2] : Array Nat).binSearch 3 natLt = none := by
  simp [Array.binSearch, Array.binSearchAux, natLt]

example : (#[1, 2, 2, 2, 4] : Array Nat).binSearch 2 natLt = some 2 := by
  simp [Array.binSearch, Array.binSearchAux, natLt]

example : (#[1, 3, 5] : Array Nat).binSearch 1 natLt = some 1 := by
  simp [Array.binSearch, Array.binSearchAux, natLt]

example : (#[1, 3, 5] : Array Nat).binSearch 5 natLt 0 99 = some 5 := by
  simp [Array.binSearch, Array.binSearchAux, natLt]

example : (#[1, 3, 5] : Array Nat).binSearch 3 natLt 2 1 = none := by decide

example : (#[1, 3, 5] : Array Nat).binSearchContains 5 natLt 0 99 = true := by
  simp [Array.binSearchContains, Array.binSearchAux, natLt]

example : (#[1, 3, 5] : Array Nat).binSearchContains 3 natLt 2 1 = false := by decide

example :
    (#[1, 3, 5] : Array Nat).binSearchContains 3 natLt 0 2 =
      ((#[1, 3, 5] : Array Nat).binSearch 3 natLt 0 2).isSome := by
  exact binSearchContains_eq_isSome _ _ _ _ _

example :
    (#[1, 2, 2, 2, 4] : Array Nat).binSearch 2 natLt 2 99 = some 2 ↔
      ∃ i, ∃ h : i < (#[1, 2, 2, 2, 4] : Array Nat).size,
        2 ≤ i ∧ i ≤ 99 ∧ (#[1, 2, 2, 2, 4] : Array Nat)[i] = 2 := by
  simpa using binSearch_eq_some_iff
    (as := (#[1, 2, 2, 2, 4] : Array Nat)) (k := 2) (a := 2) (lo := 2) (hi := 99)
    (by decide)

example :
    (#[1, 3, 5] : Array Nat).binSearch 3 natLt = some 3 ↔
      3 ∈ (#[1, 3, 5] : Array Nat) := by
  simpa using binSearch_eq_some_iff_mem
    (as := (#[1, 3, 5] : Array Nat)) (k := 3) (a := 3) (by decide)

example :
    (#[1, 3, 5] : Array Nat).binSearchContains 4 natLt = true ↔
      4 ∈ (#[1, 3, 5] : Array Nat) := by
  simpa using binSearchContains_eq_true_iff_mem
    (as := (#[1, 3, 5] : Array Nat)) (k := 4) (by decide)

example :
    (#[1, 3, 5] : Array Nat).binSearch 4 natLt = none ↔
      4 ∉ (#[1, 3, 5] : Array Nat) := by
  simpa using binSearch_eq_none_iff_not_mem
    (as := (#[1, 3, 5] : Array Nat)) (k := 4) (by decide)

end Cslib.Algorithms.Lean.BinaryTests
