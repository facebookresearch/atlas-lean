/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TatamibariDefs

namespace MetaMathlibExt.Complexity.NPComplete.Tatamibari

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : TatamibariInstance) :
    tatamibariDec (bitEncode i) = true ↔ WellFormed i ∧ TatamibariFeasible i := by
  simp [tatamibariDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : tatamibariDec [true] = false := by
  have h : bitDecode (α := TatamibariInstance) [true] = none := rfl
  simp [tatamibariDec, h]

/-- A one-by-two grid with a single `-` clue is tiled by one wide rectangle. -/
example :
    tatamibariDec (bitEncode ((1, 2, [(0, 0, 1)]) : TatamibariInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, fun _ => (0, 0, 1, 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp
  · intro j hj j' hj' hne
    simp at hj hj'
    omega
  · intro r hr c hc
    simp at hr hc
    exact ⟨0, by simp, by simp [InRect]; omega⟩
  · intro j hj j' hj'
    simp at hj hj'
    subst hj hj'
    simp [InRect]
  · intro j hj
    simp at hj
    subst hj
    simp
  · rintro ⟨p, s, hcard, hs, -⟩
    have hsub : s ⊆ Finset.range 1 := fun j hj => Finset.mem_range.2 (by simpa using hs j hj)
    have := Finset.card_le_card hsub
    simp at this
    omega

/-- The same grid with a `+` clue is rejected: the only rectangle must be the whole
one-by-two grid, which is not a square. -/
example :
    tatamibariDec (bitEncode ((1, 2, [(0, 0, 0)]) : TatamibariInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, rect, hbound, -, hcover, -, hshape, -⟩
  obtain ⟨hh, hw, hr, hc⟩ := hbound 0 (by simp)
  obtain ⟨j0, hj0, h0⟩ := hcover 0 (by simp) 0 (by simp)
  obtain ⟨j1, hj1, h1⟩ := hcover 0 (by simp) 1 (by simp)
  simp at hj0 hj1
  subst hj0 hj1
  have hsq := (hshape 0 (by simp)).1 (by simp)
  simp only [InRect] at h0 h1
  simp at hr hc
  omega

/-- The rejected instance is well formed, so the rejection comes from the clue shape. -/
example : WellFormed ((1, 2, [(0, 0, 0)]) : TatamibariInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.Tatamibari
