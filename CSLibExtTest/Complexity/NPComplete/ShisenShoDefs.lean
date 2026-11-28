/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ShisenShoDefs

namespace MetaMathlibExt.Complexity.NPComplete.ShisenSho

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ShisenShoInstance) :
    shisenShoDec (bitEncode i) = true ↔ WellFormed i ∧ ShisenShoFeasible i := by
  simp [shisenShoDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : shisenShoDec [true] = false := by
  have h : bitDecode (α := ShisenShoInstance) [true] = none := rfl
  simp [shisenShoDec, h]

/-- Two horizontally adjacent cells are connected by the single segment between them, whatever
is occupied: the segment has no other lattice point. -/
private theorem connectable_adjacent (occ : ℤ × ℤ → Prop) (r c : ℤ) :
    Connectable occ (r, c) (r, c + 1) := by
  refine ⟨(r, c + 1), (r, c + 1), Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_⟩
  rintro ⟨x, y⟩ hq ha hb
  simp only [OnSegment, min_self, max_self] at hq
  simp only [ne_eq, Prod.mk.injEq] at ha hb
  omega

/-- The row of four tiles `0 0 0 0` is cleared by removing the left pair, then the right pair;
each pair is adjacent. -/
example : shisenShoDec (bitEncode ([[0, 0, 0, 0]] : ShisenShoInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    [((0, 0), (0, 1)), ((0, 2), (0, 3))], by rfl, fun t ht => ?_⟩
  simp only [List.length_cons, List.length_nil] at ht
  rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
  · exact ⟨rfl, connectable_adjacent _ 0 0⟩
  · exact ⟨rfl, connectable_adjacent _ 0 2⟩

/-- The row `0 0` is removable as one adjacent pair, but a label occurring only twice is not a
legal layout (every label occurs exactly four times), so it is rejected. -/
example : shisenShoDec (bitEncode ([[0, 0]] : ShisenShoInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact absurd (((accepts_encoding _).1 h).1.2.2.2 0 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.ShisenSho
