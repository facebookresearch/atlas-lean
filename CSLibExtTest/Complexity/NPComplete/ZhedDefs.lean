/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ZhedDefs

namespace MetaMathlibExt.Complexity.NPComplete.Zhed

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ZhedInstance) :
    zhedDec (bitEncode i) = true ↔ WellFormed i ∧ ZhedFeasible i := by
  simp [zhedDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : zhedDec [true] = false := by
  have h : bitDecode (α := ZhedInstance) [true] = none := rfl
  simp [zhedDec, h]

/-- Moving the tile `1` in the top-left corner to the right fills the target square `(0, 1)`. -/
example : zhedDec (bitEncode (([[1, 0], [0, 0]], (0, 1)) : ZhedInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed size entry; decide, [((0, 0), 3)], by decide, by decide, ?_⟩
  decide

/-- Only the top-left square holds a tile. -/
private theorem tile_at (r c : ℕ) (h : 0 < entry (([[1, 0], [0, 0]], (1, 1)) : ZhedInstance) r c) :
    r = 0 ∧ c = 0 := by
  match r, c with
  | 0, 0 => exact ⟨rfl, rfl⟩
  | 0, c + 1 => cases c <;> simp [entry] at h
  | 1, c => rcases c with _ | _ | c <;> simp [entry] at h
  | r + 2, c => simp [entry] at h

/-- The diagonal square `(1, 1)` cannot be filled: the single tile `1` fills only `(0, 1)` or
`(1, 0)`, and each tile moves at most once. -/
example : zhedDec (bitEncode (([[1, 0], [0, 0]], (1, 1)) : ZhedInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, ms, hnd, hpos, hmem⟩
  have hfst : ∀ m ∈ ms, m.1 = (0, 0) := fun m hm => by
    obtain ⟨h₁, h₂⟩ := tile_at _ _ (hpos m hm)
    exact Prod.ext h₁ h₂
  match ms, hnd, hfst, hmem with
  | [], _, _, hmem => revert hmem; decide
  | [m], _, hfst, hmem =>
    obtain ⟨p, d⟩ := m
    obtain rfl : p = (0, 0) := hfst (p, d) (by simp)
    have hone : ∀ d : Fin 4,
        ((1 : ℤ), (1 : ℤ)) ∉ play (([[1, 0], [0, 0]], (1, 1)) : ZhedInstance) [((0, 0), d)] := by
      decide
    exact hone d hmem
  | a :: b :: _, hnd, hfst, _ =>
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd
    exact hnd.1 (Or.inl ((hfst a (by simp)).trans (hfst b (by simp)).symm))

/-- The rejected instance is well formed, so the rejection comes from unreachability. -/
example : WellFormed (([[1, 0], [0, 0]], (1, 1)) : ZhedInstance) := by
  unfold WellFormed size entry
  decide

end MetaMathlibExt.Complexity.NPComplete.Zhed
