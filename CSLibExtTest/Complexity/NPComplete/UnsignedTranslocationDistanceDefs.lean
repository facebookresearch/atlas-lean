/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UnsignedTranslocationDistanceDefs

namespace MetaMathlibExt.Complexity.NPComplete.UnsignedTranslocationDistance

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : UnsignedTranslocationDistanceInstance) :
    unsignedTranslocationDistanceDec (bitEncode i) = true ↔
      WellFormed i ∧ UnsignedTranslocationDistanceFeasible i := by
  simp [unsignedTranslocationDistanceDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : unsignedTranslocationDistanceDec [true] = false := by
  have h : bitDecode (α := UnsignedTranslocationDistanceInstance) [true] = none := rfl
  simp [unsignedTranslocationDistanceDec, h]

/-- One prefix-prefix translocation of `[1, 2]` and `[3, 4]` swaps their tails, giving
`[1, 4]` and `[3, 2]`. -/
example :
    unsignedTranslocationDistanceDec
      (bitEncode (([[1, 2], [3, 4]], [[1, 4], [3, 2]], 1) :
        UnsignedTranslocationDistanceInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, 1, le_rfl,
    fun s => if s = 0 then [[1, 2], [3, 4]] else [[1, 4], [3, 2]], rfl, ?_, ?_⟩
  · intro s hs
    obtain rfl : s = 0 := by omega
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, [1], [2], [3], [4], by decide, by decide,
      by decide, by decide, rfl, rfl, Or.inl rfl⟩
  · unfold GenomeIdentical ChromosomeIdentical
    decide

/-- With bound zero the same genomes are rejected: `[1, 2]` is neither a chromosome of
`[[1, 4], [3, 2]]` nor the reversal of one. -/
example :
    unsignedTranslocationDistanceDec
      (bitEncode (([[1, 2], [3, 4]], [[1, 4], [3, 2]], 0) :
        UnsignedTranslocationDistanceInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, t, ht, G, hG0, -, hid⟩
  obtain rfl : t = 0 := Nat.le_zero.1 ht
  rw [hG0] at hid
  revert hid
  unfold GenomeIdentical ChromosomeIdentical
  decide

/-- The rejected instance is well formed, so the rejection comes from the distance bound. -/
example :
    WellFormed (([[1, 2], [3, 4]], [[1, 4], [3, 2]], 0) : UnsignedTranslocationDistanceInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.UnsignedTranslocationDistance
