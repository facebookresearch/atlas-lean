/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeneralizedAssignmentDefs

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedAssignment

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : GeneralizedAssignmentInstance) :
    generalizedAssignmentDec (bitEncode i) = true ↔
      WellFormed i ∧ GeneralizedAssignmentFeasible i := by
  simp [generalizedAssignmentDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeneralizedAssignmentInstance) bits = none) :
    generalizedAssignmentDec bits = false := by
  simp [generalizedAssignmentDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : generalizedAssignmentDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Two jobs, two machines of capacity `2`: job `0` on machine `0` and job `1` on machine `1`
uses two units on each machine and costs `1 + 1 = 2`. -/
example :
    generalizedAssignmentDec (bitEncode
      (([[2, 3], [3, 2]], [[1, 5], [5, 1]], [2, 2], 2) : GeneralizedAssignmentInstance)) =
      true := by
  apply (accepts_encoding _).2
  exact ⟨by unfold WellFormed; decide, [0, 1], rfl, by decide, by decide, by decide⟩

/-- With capacities `1`, no machine can take a job that needs at least two units anywhere. -/
example :
    generalizedAssignmentDec (bitEncode
      (([[2, 3], [3, 2]], [[1, 5], [5, 1]], [1, 1], 10) : GeneralizedAssignmentInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, assign, -, hrange, hcap, -⟩
  have hm : assign.getD 0 0 < 2 := hrange 0 (by decide)
  have h := hcap (assign.getD 0 0) hm
  simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  generalize assign.getD 0 0 = m at hm h
  rcases m with _ | _ | m
  · simp at h; split at h <;> omega
  · simp at h; split at h <;> omega
  · omega

/-- The same jobs with capacity `2` and cost bound `1` are rejected on cost alone. -/
example :
    generalizedAssignmentDec (bitEncode
      (([[2, 3], [3, 2]], [[1, 5], [5, 1]], [2, 2], 1) : GeneralizedAssignmentInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, assign, -, hrange, -, hcost⟩
  have h0 : assign.getD 0 0 < 2 := hrange 0 (by decide)
  have h1 : assign.getD 1 0 < 2 := hrange 1 (by decide)
  simp only [List.length_cons, List.length_nil, zero_add, Finset.sum_range_succ,
    Finset.sum_range_zero] at hcost
  generalize assign.getD 0 0 = a at h0 hcost
  generalize assign.getD 1 0 = b at h1 hcost
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> first | omega | simp at hcost

end MetaMathlibExt.Complexity.NPComplete.GeneralizedAssignment
