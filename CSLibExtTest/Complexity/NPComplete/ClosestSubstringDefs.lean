/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ClosestSubstringDefs

namespace MetaMathlibExt.Complexity.NPComplete.ClosestSubstring

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ClosestSubstringInstance) :
    closestSubstringDec (bitEncode i) = true ↔ WellFormed i ∧ ClosestSubstringFeasible i := by
  simp [closestSubstringDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : closestSubstringDec [true] = false := by
  have h : bitDecode (α := ClosestSubstringInstance) [true] = none := rfl
  simp [closestSubstringDec, h]

/-- Over a binary alphabet, `11` occurs at position `1` of `0110` and at position `0` of `1100`,
so it is within distance `0` of a length-`2` substring of each. -/
example : closestSubstringDec (bitEncode
    ((2, [[0, 1, 1, 0], [1, 1, 0, 0]], 2, 0) : ClosestSubstringInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, ![1, 1], by decide, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro s (rfl | rfl)
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

/-- The strings `00` and `11` have no common length-`2` substring, so no centre is within
distance `0` of both. -/
example : closestSubstringDec (bitEncode
    ((2, [[0, 0], [1, 1]], 2, 0) : ClosestSubstringInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, t, -, h⟩
  obtain ⟨j₀, hj₀, h₀⟩ := h [0, 0] (by simp)
  obtain ⟨j₁, hj₁, h₁⟩ := h [1, 1] (by simp)
  have e₀ := congrFun (hammingDist_eq_zero.1 (Nat.le_zero.1 h₀)) 0
  have e₁ := congrFun (hammingDist_eq_zero.1 (Nat.le_zero.1 h₁)) 0
  simp only [List.length_cons, List.length_nil] at hj₀ hj₁
  obtain rfl : j₀ = 0 := by omega
  obtain rfl : j₁ = 0 := by omega
  simp [substringAt] at e₀ e₁
  omega

end MetaMathlibExt.Complexity.NPComplete.ClosestSubstring
