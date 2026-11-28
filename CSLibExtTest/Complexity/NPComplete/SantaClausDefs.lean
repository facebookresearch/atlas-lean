/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SantaClausDefs

namespace MetaMathlibExt.Complexity.NPComplete.SantaClaus

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SantaClausInstance) :
    santaClausDec (bitEncode i) = true ↔ WellFormed i ∧ SantaClausFeasible i := by
  simp [santaClausDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : santaClausDec [true] = false := by
  have h : bitDecode (α := SantaClausInstance) [true] = none := rfl
  simp [santaClausDec, h]

/-- Two agents who each value a different one of two goods at `3` can both receive value `3`:
give each agent the good it values. -/
example : santaClausDec (bitEncode ((2, [[3, 1], [1, 3]], 3) : SantaClausInstance)) = true := by
  refine (accepts_encoding _).2 ⟨⟨by simp, by simp⟩, ⟨fun j => ⟨j, by simp [j.isLt]⟩, ?_⟩⟩
  decide

/-- The same goods cannot give both agents value `4`: an agent reaches `4` only by receiving
both goods, which leaves the other agent with nothing. -/
example : santaClausDec (bitEncode ((2, [[3, 1], [1, 3]], 4) : SantaClausInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, hfeas⟩ := (accepts_encoding _).1 h
  revert hfeas
  unfold SantaClausFeasible
  decide

/-- An instance with no agents is malformed, even though the bound `0` is met vacuously. -/
example : santaClausDec (bitEncode ((0, [], 0) : SantaClausInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact ((accepts_encoding _).1 h).1.1 rfl

end MetaMathlibExt.Complexity.NPComplete.SantaClaus
