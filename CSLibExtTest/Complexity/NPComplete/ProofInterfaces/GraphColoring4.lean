/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.VertexRankingDefs

namespace MetaMathlibExt.Complexity.NPComplete.VertexRanking

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GraphColoring (GraphColoringInstance)

example (i : GraphColoringInstance) :
    vertexRankingDec (bitEncode i) = true ↔ WellFormed i ∧ VertexRankingFeasible i := by
  simp [vertexRankingDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GraphColoringInstance) bits = none) :
    vertexRankingDec bits = false := by
  simp [vertexRankingDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : vertexRankingDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : GraphColoringInstance)
    (h : ¬ WellFormed i) :
    vertexRankingDec (bitEncode i) = false := by
  simp [vertexRankingDec, bitDecode_bitEncode, h]

/-- A ranking bound larger than the vertex count is outside the instance domain. -/
example :
    vertexRankingDec (bitEncode ((2, [(0, 1)], 3) : GraphColoringInstance)) = false := by
  apply rejects_malformed _
  intro h
  exact (by decide : ¬ (3 : Nat) ≤ 2) h.2.2

end MetaMathlibExt.Complexity.NPComplete.VertexRanking
