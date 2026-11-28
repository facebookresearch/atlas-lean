/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SolitaireUnoDefs

namespace MetaMathlibExt.Complexity.NPComplete.SolitaireUno

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SolitaireUnoInstance) :
    solitaireUnoDec (bitEncode i) = true ↔ WellFormed i ∧ SolitaireUnoFeasible i := by
  simp [solitaireUnoDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : solitaireUnoDec [true] = false := by
  have h : bitDecode (α := SolitaireUnoInstance) [true] = none := rfl
  simp [solitaireUnoDec, h]

/-- A rearrangement of a list of two distinct entries is one of its two orders. -/
private theorem perm_two {α : Type} {s : List α} {x y : α} (hxy : x ≠ y) (h : s.Perm [x, y]) :
    s = [x, y] ∨ s = [y, x] := by
  have hlen := h.length_eq
  have hnd : s.Nodup := h.nodup_iff.2 (by simp [hxy])
  match s, hlen with
  | [a, b], _ =>
    have ha : a ∈ [x, y] := h.subset (by simp)
    have hb : b ∈ [x, y] := h.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    have hab : a ≠ b := by simpa using hnd
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

/-- The cards `(1,1), (2,2), (1,2)` can all be played in the order `(1,1), (1,2), (2,2)`: the
first step matches in color, the second in number. -/
example : solitaireUnoDec
    (bitEncode ((2, 2, [(1, 1), (2, 2), (1, 2)]) : SolitaireUnoInstance)) = true := by
  refine (accepts_encoding _).2
    ⟨by unfold WellFormed; decide, [(1, 1), (1, 2), (2, 2)], ?_, by decide⟩
  exact List.Perm.cons _ (List.Perm.swap _ _ [])

/-- The cards `(1,1)` and `(2,2)` share neither color nor number, so neither order works. -/
example : solitaireUnoDec
    (bitEncode ((2, 2, [(1, 1), (2, 2)]) : SolitaireUnoInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, s, hs, hchain⟩ := (accepts_encoding _).1 h
  rcases perm_two (by decide) hs with rfl | rfl <;> simp at hchain

/-- A card with color `3` is malformed when there are only `2` colors. -/
example : solitaireUnoDec (bitEncode ((2, 2, [(3, 1)]) : SolitaireUnoInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1 (3, 1) (by simp)).2.1 (by decide)

end MetaMathlibExt.Complexity.NPComplete.SolitaireUno
