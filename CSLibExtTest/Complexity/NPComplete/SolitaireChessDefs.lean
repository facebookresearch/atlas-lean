/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SolitaireChessDefs

namespace MetaMathlibExt.Complexity.NPComplete.SolitaireChess

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SolitaireChessInstance) :
    solitaireChessDec (bitEncode i) = true ↔ WellFormed i ∧ SolitaireChessFeasible i := by
  simp [solitaireChessDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : solitaireChessDec [true] = false := by
  have h : bitDecode (α := SolitaireChessInstance) [true] = none := rfl
  simp [solitaireChessDec, h]

/-- On a `2 × 2` board, a pawn on `(0, 0)` captures the rook diagonally ahead of it on
`(1, 1)`, leaving one piece. -/
example : solitaireChessDec (bitEncode ((2, [(5, 0, 0), (2, 1, 1)]) : SolitaireChessInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, [(5, 1, 1)],
    Relation.ReflTransGen.single ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, ?_, rfl⟩, rfl⟩
  simp [CanCapture, square]

/-- A pawn on `(0, 1)` and a rook on `(1, 0)`: the rook is diagonally behind the pawn, which
pawns cannot capture, and a rook does not capture diagonally, so no move is possible and two
pieces remain. -/
example : solitaireChessDec (bitEncode ((2, [(5, 0, 1), (2, 1, 0)]) : SolitaireChessInstance)) =
    false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, s, hs, hlen⟩ := (accepts_encoding _).1 h
  have stuck : ∀ s', ¬ Move [(5, 0, 1), (2, 1, 0)] s' := by
    rintro s' ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, hcap, -⟩
    simp only [List.length_cons, List.length_nil, ne_eq, Fin.mk.injEq] at ha hb hab
    rcases (by omega : a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [CanCapture, square] at hcap
  rcases Relation.ReflTransGen.cases_head hs with rfl | ⟨s', hm, -⟩
  · simp at hlen
  · exact stuck s' hm

/-- Two pieces on one square make the instance malformed. -/
example : solitaireChessDec (bitEncode ((2, [(5, 0, 0), (2, 0, 0)]) : SolitaireChessInstance)) =
    false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd ((accepts_encoding _).1 h).1.2 (by decide)

end MetaMathlibExt.Complexity.NPComplete.SolitaireChess
