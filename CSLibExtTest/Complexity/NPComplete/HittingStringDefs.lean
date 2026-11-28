/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HittingStringDefs

namespace MetaMathlibExt.Complexity.NPComplete.HittingString

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HittingStringInstance) :
    hittingStringDec (bitEncode i) = true ↔ WellFormed i ∧ HittingStringFeasible i := by
  simp [hittingStringDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := HittingStringInstance) bits = none) :
    hittingStringDec bits = false := by
  simp [hittingStringDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hittingStringDec [true] = false :=
  rejects_undecodable [true] rfl

/-- The strings `0*` and `*1` are both hit by `01`. -/
example :
    hittingStringDec (bitEncode ((2, [[0, 2], [2, 1]]) : HittingStringInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [false, true], rfl, ?_⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩

/-- No one-bit string agrees with both `0` and `1`. -/
example :
    hittingStringDec (bitEncode ((1, [[0], [1]]) : HittingStringInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, x, hx, h⟩
  obtain ⟨k, hk, hk0⟩ := h [0] (by simp)
  obtain ⟨l, hl, hl1⟩ := h [1] (by simp)
  obtain rfl : k = 0 := by omega
  obtain rfl : l = 0 := by omega
  rcases x with _ | ⟨b, _ | ⟨c, x⟩⟩
  · simp at hx
  · cases b <;> simp_all
  · simp at hx

/-- The symbol `3` is not one of `0`, `1` and `*`. -/
example :
    hittingStringDec (bitEncode ((1, [[3]]) : HittingStringInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  exact absurd (h [3] (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.HittingString
