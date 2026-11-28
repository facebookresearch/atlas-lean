/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MaximumQuadraticAssignmentDefs

namespace MetaMathlibExt.Complexity.NPComplete.MaximumQuadraticAssignment

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MaximumQuadraticAssignmentInstance) :
    maximumQuadraticAssignmentDec (bitEncode i) = true ↔
      WellFormed i ∧ MaximumQuadraticAssignmentFeasible i := by
  simp [maximumQuadraticAssignmentDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MaximumQuadraticAssignmentInstance) bits = none) :
    maximumQuadraticAssignmentDec bits = false := by
  simp [maximumQuadraticAssignmentDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : maximumQuadraticAssignmentDec [true] = false :=
  rejects_undecodable [true] rfl

/-- With `A = [[0, 1], [1, 0]]` and `B = [[0, 2], [2, 0]]`, the identity permutation reaches
`1 * 2 + 1 * 2 = 4`. -/
example :
    maximumQuadraticAssignmentDec (bitEncode
      ((2, [[0, 1], [1, 0]], [[0, 2], [2, 0]], 4) : MaximumQuadraticAssignmentInstance)) =
      true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed QuadraticAssignment.WellFormed IsSymmetric entry; decide,
    [0, 1], by decide, ?_⟩
  unfold entry
  decide

/-- Every assignment of two positions reaches at most `4`, below the bound `5`. -/
example :
    maximumQuadraticAssignmentDec (bitEncode
      ((2, [[0, 1], [1, 0]], [[0, 2], [2, 0]], 5) : MaximumQuadraticAssignmentInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, perm, hperm, hsum⟩
  have hlen : perm.length = 2 := by simpa using hperm.length_eq
  have hmem : ∀ x ∈ perm, x < 2 := fun x hx => by simpa using hperm.subset hx
  rcases perm with _ | ⟨a, _ | ⟨b, _ | ⟨c, perm⟩⟩⟩ <;> simp at hlen
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  revert hsum
  unfold entry
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> first | omega | decide

/-- An asymmetric flow matrix is malformed even though plain quadratic assignment accepts the
instance. -/
example :
    maximumQuadraticAssignmentDec (bitEncode
      ((2, [[0, 1], [1, 0]], [[0, 3], [1, 0]], 4) : MaximumQuadraticAssignmentInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, h, -⟩, -⟩
  exact absurd (h 0 (by decide) 1 (by decide)) (by unfold entry; decide)

/-- The asymmetric instance is accepted by QUADRATIC ASSIGNMENT with bound `4`. -/
example :
    QuadraticAssignment.quadraticAssignmentDec (bitEncode
      ((2, [[0, 1], [1, 0]], [[0, 3], [1, 0]], 4) : MaximumQuadraticAssignmentInstance)) =
      true := by
  simp only [QuadraticAssignment.quadraticAssignmentDec, bitDecode_bitEncode,
    decide_eq_true_eq]
  exact ⟨by unfold QuadraticAssignment.WellFormed; decide, [0, 1], by decide, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.MaximumQuadraticAssignment
