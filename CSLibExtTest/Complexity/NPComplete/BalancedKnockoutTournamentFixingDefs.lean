/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BalancedKnockoutTournamentFixingDefs

namespace MetaMathlibExt.Complexity.NPComplete.BalancedKnockoutTournamentFixing

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : BalancedKnockoutTournamentFixingInstance) :
    balancedKnockoutTournamentFixingDec (bitEncode i) = true ↔
      WellFormed i ∧ BalancedKnockoutTournamentFixingFeasible i := by
  simp [balancedKnockoutTournamentFixingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : balancedKnockoutTournamentFixingDec [true] = false := by
  have h : bitDecode (α := BalancedKnockoutTournamentFixingInstance) [true] = none := rfl
  simp [balancedKnockoutTournamentFixingDec, h]

/-- Four players: `1` beats `0`, `0` beats `2` and `3`, `2` beats `1`, `1` beats `3`, and `3`
beats `2`. -/
private abbrev beats : List (ℕ × ℕ) := [(1, 0), (0, 2), (0, 3), (2, 1), (1, 3), (3, 2)]

/-- Player `0` loses to `1` but wins under the seeding `0, 3, 1, 2`: it beats `3`, then `2`,
who has eliminated `1`. -/
example : balancedKnockoutTournamentFixingDec (bitEncode
    ((2, beats, 0) : BalancedKnockoutTournamentFixingInstance)) = true := by
  refine (accepts_encoding _).2 ⟨?_, [0, 3, 1, 2], by decide, by decide⟩
  unfold WellFormed
  simp only [← List.mem_range]
  decide

/-- Player `3` beats only `2`, and a winner of two rounds must beat two players, so no seeding
of the same tournament makes `3` win. -/
example : balancedKnockoutTournamentFixingDec (bitEncode
    ((2, beats, 3) : BalancedKnockoutTournamentFixingInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, s, hs, hw⟩
  have hn : s.Nodup := hs.nodup_iff.2 List.nodup_range
  have hm : ∀ x ∈ s, x ∈ List.range 4 := fun x hx => hs.subset hx
  match s, hs.length_eq with
  | [a, b, c, d], _ =>
    have key : ∀ a ∈ List.range 4, ∀ b ∈ List.range 4, ∀ c ∈ List.range 4,
        ∀ d ∈ List.range 4, [a, b, c, d].Nodup →
        knockoutWinner ((2, beats, 3) : BalancedKnockoutTournamentFixingInstance) 2
          [a, b, c, d] ≠ 3 := by
      decide
    exact key a (hm a (by simp)) b (hm b (by simp)) c (hm c (by simp)) d (hm d (by simp)) hn hw

end MetaMathlibExt.Complexity.NPComplete.BalancedKnockoutTournamentFixing
