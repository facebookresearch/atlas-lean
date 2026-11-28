/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShortestCommonSuperstringBinaryDefs

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringBinary

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open ShortestCommonSuperstring (ShortestCommonSuperstringInstance)

example (i : ShortestCommonSuperstringInstance) :
    shortestCommonSuperstringBinaryDec (bitEncode i) = true ↔
      WellFormed i ∧ ShortestCommonSuperstring.ShortestCommonSuperstringFeasible i := by
  simp [shortestCommonSuperstringBinaryDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := ShortestCommonSuperstringInstance) bits = none) :
    shortestCommonSuperstringBinaryDec bits = false := by
  simp [shortestCommonSuperstringBinaryDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shortestCommonSuperstringBinaryDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : ShortestCommonSuperstringInstance)
    (h : ¬ WellFormed i) :
    shortestCommonSuperstringBinaryDec (bitEncode i) = false := by
  simp [shortestCommonSuperstringBinaryDec, bitDecode_bitEncode, h]

/-- The binary language rejects a word containing the symbol two. -/
example :
    shortestCommonSuperstringBinaryDec
      (bitEncode ((2, [[2]], 1) : ShortestCommonSuperstringInstance)) =
        false := by
  apply rejects_malformed _
  intro h
  exact (by decide : ¬ (2 : Nat) < 2) (h.1.1 [2] (by simp) 2 (by simp))

/-- The two binary letters fit in a single superstring of length two. -/
example :
    shortestCommonSuperstringBinaryDec
      (bitEncode ((2, [[0], [1]], 2) : ShortestCommonSuperstringInstance)) = true := by
  let i : ShortestCommonSuperstringInstance := (2, [[0], [1]], 2)
  have hw : WellFormed i := by
    unfold WellFormed ShortestCommonSuperstring.WellFormed
    decide
  have hf : ShortestCommonSuperstring.ShortestCommonSuperstringFeasible i := by
    refine ⟨[0, 1], ?_, ?_, ?_⟩ <;> decide
  change shortestCommonSuperstringBinaryDec (bitEncode i) = true
  simp [shortestCommonSuperstringBinaryDec, hw, hf]

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringBinary
