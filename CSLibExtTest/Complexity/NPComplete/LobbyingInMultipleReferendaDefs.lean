/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.LobbyingInMultipleReferendaDefs

namespace MetaMathlibExt.Complexity.NPComplete.LobbyingInMultipleReferenda

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : LobbyingInMultipleReferendaInstance) :
    lobbyingInMultipleReferendaDec (bitEncode i) = true ↔
      WellFormed i ∧ LobbyingInMultipleReferendaFeasible i := by
  simp [lobbyingInMultipleReferendaDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := LobbyingInMultipleReferendaInstance) bits = none) :
    lobbyingInMultipleReferendaDec bits = false := by
  simp [lobbyingInMultipleReferendaDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : lobbyingInMultipleReferendaDec [true] = false :=
  rejects_undecodable [true] rfl

/-- Three voters on two issues, target `yes, no`: changing voter `0` to `yes, no` gives strict
majorities `2 / 3` for `yes` on issue `0` and `2 / 3` for `no` on issue `1`. -/
example :
    lobbyingInMultipleReferendaDec (bitEncode
      (([[false, true], [false, false], [true, true]], [true, false], 1) :
        LobbyingInMultipleReferendaInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, {0}, rfl,
    fun r j => if r = 0 then [true, false].getD j false
      else ([[false, true], [false, false], [true, true]].get r).getD j false, ?_, ?_⟩
  · intro r hr j
    simp only [Finset.mem_singleton] at hr
    simp [hr, vote]
  · unfold target
    decide

/-- Three voters all voting `no`: changing one voter yields only one `yes`, not a majority. -/
example :
    lobbyingInMultipleReferendaDec (bitEncode
      (([[false], [false], [false]], [true], 1) :
        LobbyingInMultipleReferendaInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, S, hcard, F, hkeep, hmaj⟩
  let i : LobbyingInMultipleReferendaInstance := ([[false], [false], [false]], [true], 1)
  have key : ∀ (r : Voter i) (j : Issue i), target i j ≠ vote i r j := by
    unfold vote target; decide
  let j : Issue i := ⟨0, by decide⟩
  have hsub : (Finset.univ.filter fun r => F r j = target _ j) ⊆ S := by
    intro r hr
    by_contra hrS
    have h1 := hkeep r hrS j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [hr] at h1
    exact key r j h1
  have h1 := Finset.card_le_card hsub
  have h2 : 3 < 2 * (Finset.univ.filter fun r => F r j = target i j).card := hmaj j
  have h3 : S.card = 1 := hcard
  omega

/-- A budget larger than the number of voters is malformed. -/
example :
    lobbyingInMultipleReferendaDec (bitEncode
      (([[false]], [true], 2) : LobbyingInMultipleReferendaInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, h⟩, -⟩
  exact absurd h (by decide)

end MetaMathlibExt.Complexity.NPComplete.LobbyingInMultipleReferenda
