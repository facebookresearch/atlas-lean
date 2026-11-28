/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.IntersectionPatternDiagonalThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionPatternDiagonalThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.IntersectionPattern

private theorem accepts_encoding (A : IntersectionPatternInstance) :
    intersectionPatternDiagonalThreeDec (bitEncode A) = true ↔
      WellFormed A ∧ IntersectionPatternFeasible A := by
  simp [intersectionPatternDiagonalThreeDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := IntersectionPatternInstance) bits = none) :
    intersectionPatternDiagonalThreeDec bits = false := by
  simp [intersectionPatternDiagonalThreeDec, h]

/-- A lone continuation bit is a truncated row block. -/
example : intersectionPatternDiagonalThreeDec [true] = false :=
  rejects_undecodable [true] rfl

/-- The sets `{0, 1, 2}` and `{2, 3, 4}` realize the pattern `[[3, 1], [1, 3]]`. -/
example :
    intersectionPatternDiagonalThreeDec
      (bitEncode ([[3, 1], [1, 3]] : IntersectionPatternInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed IntersectionPattern.WellFormed; decide,
    fun k => if k.val = 0 then {0, 1, 2} else {2, 3, 4}, ?_⟩
  decide

/-- Two three-element sets cannot share four elements. -/
example :
    intersectionPatternDiagonalThreeDec
      (bitEncode ([[3, 4], [4, 3]] : IntersectionPatternInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, C, hC⟩
  have h00 := hC ⟨0, by decide⟩ ⟨0, by decide⟩
  have h01 := hC ⟨0, by decide⟩ ⟨1, by decide⟩
  simp only [Finset.inter_self] at h00
  have := Finset.card_le_card (Finset.inter_subset_left (s₁ := C ⟨0, by decide⟩)
    (s₂ := C ⟨1, by decide⟩))
  simp_all

/-- A realizable pattern with diagonal entry `2` is outside the restricted language. -/
example :
    intersectionPatternDiagonalThreeDec
      (bitEncode ([[2]] : IntersectionPatternInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, h⟩, -⟩
  exact absurd (h ⟨0, by decide⟩) (by decide)

/-- The same pattern `[[2]]` is accepted by unrestricted INTERSECTION PATTERN. -/
example :
    intersectionPatternDec (bitEncode ([[2]] : IntersectionPatternInstance)) = true := by
  simp only [intersectionPatternDec, bitDecode_bitEncode, decide_eq_true_eq]
  exact ⟨by unfold IntersectionPattern.WellFormed; decide, fun _ => {0, 1}, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.IntersectionPatternDiagonalThree
