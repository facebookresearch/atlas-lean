/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.KlondikeSolitaireDefs

namespace MetaMathlibExt.Complexity.NPComplete.KlondikeSolitaire

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.FreeCell (Card deck Matches)

private theorem accepts_encoding (i : KlondikeSolitaireInstance) :
    klondikeSolitaireDec (bitEncode i) = true ↔
      WellFormed i ∧ KlondikeSolitaireFeasible i := by
  simp [klondikeSolitaireDec, bitDecode_bitEncode]

/-- Rule 2 for a build stack holding just the face-up card `c`. -/
private theorem step_lone_to_suit (n : ℕ) (s : Config) (j : ℕ) (c : Card) (h : ℕ)
    (hb : s.builds[j]? = some ([], [c])) (hs : s.suits[c.1]? = some h) (hc : c.2 = h + 1) :
    Step n s { s with builds := s.builds.set j ([], []), suits := s.suits.set c.1 c.2 } :=
  Or.inr (Or.inl ⟨j, [], [], c, h, by simpa using hb, hs, hc, rfl⟩)

/-- Four one-card build stacks holding the four aces of a one-card-per-suit deck. -/
private abbrev aces : KlondikeSolitaireInstance := (1, [[(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)]], [])

/-- One build stack holding the whole two-card-per-suit deck, aces at the bottom and the
`♠ 2` on top. -/
private abbrev buried : KlondikeSolitaireInstance :=
  (2, [[(0, 1), (1, 1), (2, 1), (3, 1), (0, 2), (1, 2), (2, 2), (3, 2)]], [])

/-- In the buried deal the only legal move redeals the empty talon, which changes nothing. -/
private theorem step_buried {t : Config} (h : Step 2 (init buried) t) : t = init buried := by
  rcases h with ⟨j, k, d, u, x, hjk, hj, hk, -, -⟩ | ⟨j, d, u, c, h, hj, hs, hc, -⟩ |
    ⟨j, x, q, h, -, hq, -, -⟩ | ⟨hp, -⟩ | ⟨-, rfl⟩ | ⟨r, c, ht, -⟩
  · rcases j with _ | j
    · rcases k with _ | k
      · exact absurd rfl hjk
      · simp [init] at hk
    · simp [init] at hj
  · rcases j with _ | j
    swap
    · simp [init] at hj
    simp only [init, List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hj
    obtain ⟨-, hu⟩ := hj
    have hc' : c = (3, 2) := by
      cases u with
      | nil => simpa using hu.symm
      | cons a u => simp at hu
    subst hc'
    simp [init] at hs
    omega
  · rcases q with _ | _ | _ | _ | q <;> simp [init] at hq
  · exact absurd rfl hp
  · rfl
  · simp [init] at ht

/-- A lone continuation bit is a truncated instance encoding. -/
example : klondikeSolitaireDec [true] = false := by
  have h : bitDecode (α := KlondikeSolitaireInstance) [true] = none := rfl
  simp [klondikeSolitaireDec, h]

/-- The four aces start face up and go straight to their suit stacks. -/
example : klondikeSolitaireDec (bitEncode aces) = true := by
  apply (accepts_encoding _).2
  refine ⟨⟨le_refl _, by decide, by decide⟩, _,
    ((((Relation.ReflTransGen.refl.tail
      (step_lone_to_suit 1 _ 0 (0, 1) 0 rfl rfl rfl)).tail
      (step_lone_to_suit 1 _ 1 (1, 1) 0 rfl rfl rfl)).tail
      (step_lone_to_suit 1 _ 2 (2, 1) 0 rfl rfl rfl)).tail
      (step_lone_to_suit 1 _ 3 (3, 1) 0 rfl rfl rfl)), rfl⟩

/-- The buried deal is a legal deal: it holds each card of the two-card-per-suit deck once. -/
example : WellFormed buried := ⟨by decide, by decide, by decide⟩

/-- With every card in one build stack, the aces are face down under the `♠ 2`: no move changes
the initial configuration, so no suit stack ever grows. -/
example : klondikeSolitaireDec (bitEncode buried) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, t, hreach, hwin⟩ := (accepts_encoding _).1 hacc
  have hstuck : ∀ t', Relation.ReflTransGen (Step 2) (init buried) t' → t' = init buried := by
    intro t' h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      subst ih
      exact step_buried hstep
  rw [hstuck t hreach] at hwin
  simp [init] at hwin

end MetaMathlibExt.Complexity.NPComplete.KlondikeSolitaire
