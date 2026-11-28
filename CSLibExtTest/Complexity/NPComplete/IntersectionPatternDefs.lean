/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.IntersectionPatternDefs

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionPattern

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (A : IntersectionPatternInstance) :
    intersectionPatternDec (bitEncode A) = true ↔
      WellFormed A ∧ IntersectionPatternFeasible A := by
  simp [intersectionPatternDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := IntersectionPatternInstance) bits = none) :
    intersectionPatternDec bits = false := by
  simp [intersectionPatternDec, h]

/-- A lone continuation bit is a truncated row block. -/
example : intersectionPatternDec [true] = false :=
  rejects_undecodable [true] rfl

/-- The sets `{0, 1}` and `{1}` realize the pattern `[[2, 1], [1, 1]]`. -/
example :
    intersectionPatternDec (bitEncode ([[2, 1], [1, 1]] : IntersectionPatternInstance)) =
      true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, fun k => if k.val = 0 then {0, 1} else {1}, ?_⟩
  decide

/-- An intersection of size two cannot lie inside a set of size one. -/
example :
    intersectionPatternDec (bitEncode ([[1, 2], [2, 1]] : IntersectionPatternInstance)) =
      false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, C, hC⟩
  have h00 := hC ⟨0, by decide⟩ ⟨0, by decide⟩
  have h01 := hC ⟨0, by decide⟩ ⟨1, by decide⟩
  simp only [Finset.inter_self] at h00
  have := Finset.card_le_card (Finset.inter_subset_left (s₁ := C ⟨0, by decide⟩)
    (s₂ := C ⟨1, by decide⟩))
  simp_all

/-- A non-square matrix is malformed even though it has a single row. -/
example :
    intersectionPatternDec (bitEncode ([[0, 0]] : IntersectionPatternInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  exact absurd (h [0, 0] (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.IntersectionPattern
