/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DodgsonScoreDefs

namespace MetaMathlibExt.Complexity.NPComplete.DodgsonScore

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.GameTheory.SocialChoice.ArrowWanted (Profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers supporters)

private theorem accepts_encoding (i : DodgsonScoreInstance) :
    dodgsonScoreDec (bitEncode i) = true ↔ WellFormed i ∧ DodgsonScoreFeasible i := by
  simp [dodgsonScoreDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : dodgsonScoreDec [true] = false := by
  have h : bitDecode (α := DodgsonScoreInstance) [true] = none := rfl
  simp [dodgsonScoreDec, h]

/-- The order `0 ≻ 1` on two candidates. -/
private def zeroFirst : MathlibExt.Order.StrictTotalOrder (Fin 2) where
  lt a b := a.1 < b.1
  irrefl _ := Nat.lt_irrefl _
  trans := Nat.lt_trans
  total {a b} h := by
    have : a.1 ≠ b.1 := fun e => h (Fin.ext e)
    omega

/-- One voter ranks `1 ≻ 0`; one switch of the top two positions makes `0` the unanimous, hence
Condorcet, winner. -/
example : dodgsonScoreDec (bitEncode ((2, 0, [[1, 0]], 1) : DodgsonScoreInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, [(0, 0)], by decide,
    by decide, (fun _ => zeroFirst : Profile (Fin 2) (Fin 1)), ?_, ?_⟩
  · intro v a b
    change a.1 < b.1 ↔ _
    revert v a b
    decide
  · intro a d ha hd
    obtain rfl : a = 0 := Fin.ext ha
    obtain rfl : d = 1 := by
      obtain ⟨_ | _ | d, hd'⟩ := d
      · exact absurd rfl hd
      · rfl
      · omega
    unfold MajorityPrefers
    rw [Fintype.card_fin]
    refine Nat.lt_of_lt_of_le (m := 2 * 1) (by decide)
      (Nat.mul_le_mul_left 2 (Finset.card_pos.2 ⟨⟨0, Nat.zero_lt_one⟩, ?_⟩))
    classical
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.zero_lt_one⟩

/-- In a profile, a voter whose list ranks `1` before `0` does not prefer `0` to `1`. -/
private theorem not_lt_of_list {V : List (List ℕ)} {R : Profile (Fin 2) (Fin V.length)}
    (hR : ∀ v a b, (R v).lt a b ↔ (V.get v).idxOf a.1 < (V.get v).idxOf b.1)
    (v : Fin V.length) (hv : V.get v = [1, 0]) : ¬ (R v).lt 0 1 := by
  rw [hR, hv]
  decide

/-- Two voters rank `1 ≻ 0`. Candidate `0` needs both voters, hence two switches, so budget one
does not suffice. -/
example : dodgsonScoreDec (bitEncode ((2, 0, [[1, 0], [1, 0]], 1) : DodgsonScoreInstance)) =
    false := by
  cases h : dodgsonScoreDec (bitEncode ((2, 0, [[1, 0], [1, 0]], 1) : DodgsonScoreInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, S, hlen, hS, R, hR, hwin⟩ := (accepts_encoding _).1 h
    have hmaj := hwin 0 1 rfl (by decide)
    -- after at most one switch, some voter still ranks `1 ≻ 0`
    obtain ⟨v, hv⟩ : ∃ v : Fin (S.foldl applySwitch [[1, 0], [1, 0]]).length,
        (S.foldl applySwitch [[1, 0], [1, 0]]).get v = [1, 0] := by
      match S, hlen, hS with
      | [], _, _ => exact ⟨⟨0, by decide⟩, rfl⟩
      | [(w, p)], _, hS =>
        obtain ⟨hw, hp⟩ := hS (w, p) (List.mem_singleton_self _)
        simp only at hw hp
        obtain rfl : p = 0 := by omega
        obtain rfl | rfl : w = 0 ∨ w = 1 := by simp at hw; omega
        · exact ⟨⟨1, by decide⟩, rfl⟩
        · exact ⟨⟨0, by decide⟩, rfl⟩
    have hlt : (supporters R 0 1).card < (S.foldl applySwitch [[1, 0], [1, 0]]).length := by
      classical
      refine lt_of_lt_of_eq (Finset.card_lt_card (Finset.filter_ssubset.2
        ⟨v, Finset.mem_univ _, not_lt_of_list hR v hv⟩)) ?_
      rw [Finset.card_univ, Fintype.card_fin]
    have hl : (S.foldl applySwitch [[1, 0], [1, 0]]).length = 2 := by
      clear hmaj hlt hv hwin hR R
      match S, hlen, hS with
      | [], _, _ => rfl
      | [(w, p)], _, _ => simp [applySwitch]
    unfold MajorityPrefers at hmaj
    rw [Fintype.card_fin] at hmaj
    have hl' : (S.foldl applySwitch (2, 0, [[1, 0], [1, 0]], 1).2.2.1).length = 2 := hl
    omega

end MetaMathlibExt.Complexity.NPComplete.DodgsonScore
