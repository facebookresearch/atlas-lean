/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShortestCommonSuperstringDefs

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ShortestCommonSuperstringInstance) :
    shortestCommonSuperstringDec (bitEncode i) = true ↔
      WellFormed i ∧ ShortestCommonSuperstringFeasible i := by
  simp [shortestCommonSuperstringDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shortestCommonSuperstringDec [true] = false := by
  have h : bitDecode (α := ShortestCommonSuperstringInstance) [true] = none := rfl
  simp [shortestCommonSuperstringDec, h]

/-- The strings `01` and `10` overlap in `010`, a superstring of length `3`. -/
example : shortestCommonSuperstringDec
    (bitEncode ((2, [[0, 1], [1, 0]], 3) : ShortestCommonSuperstringInstance)) = true := by
  refine (accepts_encoding _).2 ⟨⟨by decide, by decide⟩, [0, 1, 0], by decide, by decide, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨⟨[], [0], rfl⟩, ⟨[0], [], rfl⟩⟩

/-- No string of length `2` contains both `01` and `10`: it would have to equal each of them. -/
example : shortestCommonSuperstringDec
    (bitEncode ((2, [[0, 1], [1, 0]], 2) : ShortestCommonSuperstringInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, w, -, hlen, hsub⟩ := (accepts_encoding _).1 h
  have h01 : [0, 1] <:+: w := hsub _ (by simp)
  have h10 : [1, 0] <:+: w := hsub _ (by simp)
  have hw : w.length = 2 := le_antisymm hlen (by simpa using h01.length_le)
  have e1 := h01.eq_of_length (by simp [hw])
  have e2 := h10.eq_of_length (by simp [hw])
  simp [← e1] at e2

/-- The bound `0` is malformed, even for an empty set of strings. -/
example : shortestCommonSuperstringDec
    (bitEncode ((2, [], 0) : ShortestCommonSuperstringInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.2 (by decide)

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring
