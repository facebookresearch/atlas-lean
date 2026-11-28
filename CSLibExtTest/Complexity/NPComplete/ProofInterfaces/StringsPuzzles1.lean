/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShuffleSquareDefs

namespace MetaMathlibExt.Complexity.NPComplete.ShuffleSquare

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ShuffleSquareInstance) :
    shuffleSquareDec (bitEncode i) = true ↔ WellFormed i ∧ ShuffleSquareFeasible i := by
  simp [shuffleSquareDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := ShuffleSquareInstance) bits = none) :
    shuffleSquareDec bits = false := by
  simp [shuffleSquareDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shuffleSquareDec [true] = false :=
  rejects_undecodable [true] rfl

/-- The word `7 7` is a shuffle of two copies of the one-letter word `7`. -/
example : shuffleSquareDec (bitEncode ([7, 7] : ShuffleSquareInstance)) = true := by
  apply (accepts_encoding _).2
  exact ⟨trivial, [7], .left 7 (.right 7 .nil)⟩

end MetaMathlibExt.Complexity.NPComplete.ShuffleSquare
