/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.StableRoommatesWithTiesDefs

namespace MetaMathlibExt.Complexity.NPComplete.StableRoommatesWithTies

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : StableRoommatesWithTiesInstance) :
    stableRoommatesWithTiesDec (bitEncode i) = true ↔
      WellFormed i ∧ StableRoommatesWithTiesFeasible i := by
  simp [stableRoommatesWithTiesDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : stableRoommatesWithTiesDec [true] = false := by
  have h : bitDecode (α := StableRoommatesWithTiesInstance) [true] = none := rfl
  simp [stableRoommatesWithTiesDec, h]

/-- Four agents: `0` and `1` rank each other first, `2` and `3` rank each other first, and each
ranks the other two agents in a tie. Matching `0–1` and `2–3` is blocked by no pair. -/
example : stableRoommatesWithTiesDec (bitEncode ((4,
    [[3, 0, 1, 1], [0, 3, 1, 1], [1, 1, 3, 0], [1, 1, 0, 3]]) :
      StableRoommatesWithTiesInstance)) = true := by
  refine (accepts_encoding _).2 ⟨⟨rfl, by decide⟩,
    fun v => if v = 0 then 1 else if v = 1 then 0 else if v = 2 then 3 else 2, ?_, ?_⟩
  · unfold Function.Involutive; decide
  · unfold Blocks; decide

/-- Three agents with cyclic preferences (`0` prefers `1`, `1` prefers `2`, `2` prefers `0`)
have no stable matching: someone is unmatched, and every matching is blocked. -/
example : stableRoommatesWithTiesDec (bitEncode ((3,
    [[2, 0, 1], [1, 2, 0], [0, 1, 2]]) : StableRoommatesWithTiesInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, μ, hinv, hstable⟩ := (accepts_encoding _).1 h
  revert μ
  unfold Function.Involutive Blocks
  decide

/-- A rank table with a missing row is malformed, even though a lone agent is trivially
stable. -/
example : stableRoommatesWithTiesDec (bitEncode ((1, []) : StableRoommatesWithTiesInstance)) =
    false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.StableRoommatesWithTies
