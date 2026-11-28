/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ThreeDimensionalAssignmentDefs

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalAssignment

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ThreeDimensionalAssignmentInstance) :
    threeDimensionalAssignmentDec (bitEncode i) = true ↔
      WellFormed i ∧ ThreeDimensionalAssignmentFeasible i := by
  simp [threeDimensionalAssignmentDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : threeDimensionalAssignmentDec [true] = false := by
  have h : bitDecode (α := ThreeDimensionalAssignmentInstance) [true] = none := rfl
  simp [threeDimensionalAssignmentDec, h]

/-- The `2 × 2 × 2` cost table with cost `1` on `(0, 0, 0)` and `(1, 1, 1)` and cost `5`
elsewhere. -/
private abbrev table : List (List (List ℕ)) := [[[1, 5], [5, 5]], [[5, 5], [5, 1]]]

/-- The diagonal assignment `{(0, 0, 0), (1, 1, 1)}` costs `2`. -/
example :
    threeDimensionalAssignmentDec
      (bitEncode ((2, 2, 2, table, 2) : ThreeDimensionalAssignmentInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, {(0, 0, 0), (1, 1, 1)}, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

/-- Bound `1` is rejected: every assignment has two triples, each costing at least `1`. -/
example :
    threeDimensionalAssignmentDec
      (bitEncode ((2, 2, 2, table, 1) : ThreeDimensionalAssignmentInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, A, hx, -, -, hcost⟩
  have hcard : A.card = 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun t => t.1) (t := Finset.univ) (by simp)]
    simp [hx]
  have hpos : ∀ t : Triple (2, 2, 2, table, 1), 1 ≤ cost (2, 2, 2, table, 1) t := by decide
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
  rw [Finset.sum_pair hab] at hcost
  have ha := hpos a
  have hb := hpos b
  simp at hcost
  omega

/-- The rejected instance is well formed, so the rejection comes from the cost bound. -/
example : WellFormed ((2, 2, 2, table, 1) : ThreeDimensionalAssignmentInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalAssignment
