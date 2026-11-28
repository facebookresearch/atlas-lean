/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FreeCellDefs

namespace MetaMathlibExt.Complexity.NPComplete.FreeCell

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : FreeCellInstance) :
    freeCellDec (bitEncode i) = true ↔ WellFormed i ∧ FreeCellFeasible i := by
  simp [freeCellDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : freeCellDec [true] = false := by
  have h : bitDecode (α := FreeCellInstance) [true] = none := rfl
  simp [freeCellDec, h]

/-- The `1`-deck in one pile, tableau width `1` and no free cells. -/
private abbrev small : FreeCellInstance := (1, 1, 0, [[(0, 1), (1, 1), (2, 1), (3, 1)]])

/-- Moving the top card of a pile with at least two cards to the foundation. -/
private theorem move_top {i : FreeCellInstance} {b : List Card} {x : Card} (hb : b ≠ [])
    (hx : ∀ y ∈ b, y.1 = x.1 → ¬ y.2 < x.2) : Move i ([b ++ [x]], []) ([b], []) :=
  ⟨x, ([b], []), Or.inr (Or.inr ⟨[], [], b, hb, rfl, rfl⟩),
    Or.inr (Or.inr (Or.inr ⟨by simpa using hx, rfl⟩))⟩

/-- Every card of the `1`-deck is an ace: the top card goes to the foundation four times. -/
example : freeCellDec (bitEncode small) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, ?_⟩
  refine .head (move_top (b := [(0, 1), (1, 1), (2, 1)]) (by simp) (by decide)) ?_
  refine .head (move_top (b := [(0, 1), (1, 1)]) (by simp) (by decide)) ?_
  refine .head (move_top (b := [(0, 1)]) (by simp) (by decide)) ?_
  exact .head ⟨(0, 1), ([], []), Or.inr (Or.inl ⟨[], [], rfl, rfl⟩),
    Or.inr (Or.inr (Or.inr ⟨by simp, rfl⟩))⟩ .refl

/-- The `2`-deck in one pile with the two of diamonds on top and the ace of diamonds at the
bottom, tableau width `1` and no free cells. -/
private abbrev stuck : FreeCellInstance :=
  (2, 1, 0, [[(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (0, 2)]])

/-- The only card that can be picked up is the two of diamonds, and it cannot be dropped: there is
no free cell, no room for a new pile, no matching pile, and the ace of diamonds is still out. -/
example : freeCellDec (bitEncode stuck) = false := by
  have h : ¬ FreeCellFeasible stuck := by
    intro hp
    rcases Relation.ReflTransGen.cases_head hp with heq | ⟨s, ⟨x, t, hpick, hdrop⟩, -⟩
    · simp at heq
    rcases hpick with ⟨A, B, hA, -⟩ | ⟨P, Q, hP, -⟩ | ⟨P, Q, b, -, hP, rfl⟩
    · simp at hA
    · rcases P with _ | ⟨p, P⟩
      · simp at hP
      · simp at hP
    · rcases P with _ | ⟨p, P⟩
      · simp only [List.nil_append, List.cons.injEq] at hP
        obtain ⟨hpile, rfl⟩ := hP
        have hx : x = (0, 2) := by simpa using (congrArg List.getLast? hpile).symm
        have hb : b = [(0, 1), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)] := by
          simpa using (congrArg List.dropLast hpile).symm
        subst hx hb
        rcases hdrop with ⟨-, -, -, hc, -⟩ | ⟨-, -, -, hw, -⟩ | ⟨P, Q, q, hq, hm, -⟩ | ⟨hf, -⟩
        · simp at hc
        · simp at hw
        · rcases P with _ | ⟨p, P⟩
          · simp only [List.nil_append, List.cons.injEq] at hq
            obtain ⟨rfl, -⟩ := hq
            obtain ⟨b', y, hy, -, hv⟩ := hm
            have : y = (3, 2) := by simpa using (congrArg List.getLast? hy).symm
            subst this
            simp at hv
          · simp at hq
        · exact hf (0, 1) (by simp) rfl (by decide)
      · simp at hP
  simpa [freeCellDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.FreeCell
