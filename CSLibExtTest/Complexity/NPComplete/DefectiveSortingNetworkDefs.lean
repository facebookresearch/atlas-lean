/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DefectiveSortingNetworkDefs

namespace MetaMathlibExt.Complexity.NPComplete.DefectiveSortingNetwork

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Algorithms.Lean.SortingNetworks (Sorts run sortsBool sorts_of_sortsBool)

/-- On an encoded instance the language is well-formedness and feasibility. -/
private theorem dec_bitEncode (i : DefectiveSortingNetworkInstance) :
    defectiveSortingNetworkDec (bitEncode i) = true ↔
      WellFormed i ∧ DefectiveSortingNetworkFeasible i := by
  simp [defectiveSortingNetworkDec, bitDecode_bitEncode]

/-- The integer input with value `l[k]` on variable `k`. -/
private def input (n : ℕ) (l : List ℤ) : Fin n → ℤ := fun k => l.getD k 0

/-- Two bubble passes on three variables that omit the final comparison of `0` and `1`. -/
private abbrev truncatedBubble : DefectiveSortingNetworkInstance := (3, [(0, 1), (1, 2)])

/-- The full bubble sort on three variables. -/
private abbrev bubble3 : DefectiveSortingNetworkInstance := (3, [(0, 1), (1, 2), (0, 1)])

example : WellFormed truncatedBubble := by unfold WellFormed; decide

example : WellFormed bubble3 := by unfold WellFormed; decide

/-- The input `1, 2, 0` leaves the truncated program with output `1, 0, 2`. -/
private theorem truncatedBubble_output :
    run (network truncatedBubble) (input 3 [1, 2, 0]) = input 3 [1, 0, 2] := by
  funext k
  revert k
  decide

/-- Yes-instance: the input `1, 2, 0` witnesses that the truncated program does not sort. -/
example : defectiveSortingNetworkDec (bitEncode truncatedBubble) = true := by
  refine (dec_bitEncode _).2 ⟨by unfold WellFormed; decide, fun h => ?_⟩
  have := h (input 3 [1, 2, 0]) (show (0 : Fin 3) ≤ 1 by decide)
  rw [truncatedBubble_output] at this
  exact absurd this (by decide)

/-- No-instance: the full bubble sort sorts every integer input (by the 0-1 principle). -/
example : defectiveSortingNetworkDec (bitEncode bubble3) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact ((dec_bitEncode _).1 h).2 (sorts_of_sortsBool (by decide) ℤ)

/-- The statement `(1, 0)` reverses two variables, so the program does not sort. -/
private theorem reversed_not_sorts : ¬ Sorts (network (2, [(1, 0)])) ℤ := by
  intro h
  have := h (input 2 [0, 1]) (show (0 : Fin 2) ≤ 1 by decide)
  revert this
  decide

/-- Malformed: a statement `(i, j)` needs `i < j`, so the reversing program is rejected although
it does not sort. -/
example : defectiveSortingNetworkDec (bitEncode ((2, [(1, 0)]) : DefectiveSortingNetworkInstance)) =
    false := by
  rw [Bool.eq_false_iff]
  intro h
  have := ((dec_bitEncode _).1 h).1
  revert this
  unfold WellFormed
  decide

example : DefectiveSortingNetworkFeasible (2, [(1, 0)]) := reversed_not_sorts

/-- A lone continuation bit is a truncated instance encoding. -/
example : bitDecode (α := DefectiveSortingNetworkInstance) [true] = none := rfl

/-- Undecodable: the language rejects the lone bit `[true]`. -/
example : defectiveSortingNetworkDec [true] = false := rfl

end MetaMathlibExt.Complexity.NPComplete.DefectiveSortingNetwork
