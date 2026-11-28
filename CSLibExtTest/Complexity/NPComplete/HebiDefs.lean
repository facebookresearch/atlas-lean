/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HebiDefs

namespace MetaMathlibExt.Complexity.NPComplete.Hebi

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HebiInstance) :
    hebiDec (bitEncode i) = true ↔ WellFormed i ∧ HebiFeasible i := by
  simp [hebiDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hebiDec [true] = false := by
  have h : bitDecode (α := HebiInstance) [true] = none := rfl
  simp [hebiDec, h]

/-- A white square. -/
private abbrev w : Square := (false, 0, 0)

/-- Five white squares and a black square with the number `5` and an arrow pointing left. -/
private abbrev row : HebiInstance := [[w, w, w, w, w, (true, 6, 3)]]

/-- One snake with its head at the left end: its tail, square `4`, is the nearest numbered square
to the left of the black square, which therefore shows `5`. -/
example : hebiDec (bitEncode row) = true := by
  refine (accepts_encoding _).2
    ⟨by unfold WellFormed; decide, [[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]], by simp, ?_⟩
  unfold Solves Adjacent
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    refine ⟨rfl, by decide, by decide, ?_⟩
    decide
  · intro a ha b hb hab
    simp only [List.length_singleton] at ha hb
    omega
  · decide
  · decide

/-- The black square indeed sees the tail of that snake first. -/
example : ray row (0, 5) 3 = [(0, 4), (0, 3), (0, 2), (0, 1), (0, 0)] := by decide

/-- A row of four white squares is well formed, but a snake needs five distinct white squares,
so no nonempty list of snakes exists. -/
example : hebiDec (bitEncode ([[w, w, w, w]] : HebiInstance)) = false := by
  have h : ¬ HebiFeasible [[w, w, w, w]] := by
    rintro ⟨S, hne, snakes, -⟩
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil S hne
    obtain ⟨hlen, hnd, hwhite, -⟩ := snakes s hs
    have hsub : s ⊆ [(0, 0), (0, 1), (0, 2), (0, 3)] := fun x hx => by
      have := hwhite x hx
      obtain ⟨x₁, x₂⟩ := x
      simp [white, rows, cols] at this
      simp
      omega
    have := (hnd.subperm hsub).length_le
    simp at this
    omega
  simpa [hebiDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.Hebi
