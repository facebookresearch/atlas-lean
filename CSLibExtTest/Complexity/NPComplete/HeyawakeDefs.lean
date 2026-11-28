/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HeyawakeDefs
-- Decidability of connectivity on finite graphs, used to check that the white cells are
-- interconnected.
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace MetaMathlibExt.Complexity.NPComplete.Heyawake

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Adjacency in a box product of graphs with decidable adjacency is decidable. -/
local instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α)
    (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := fun _ _ =>
  decidable_of_iff' _ SimpleGraph.boxProd_adj

private theorem accepts_encoding (i : HeyawakeInstance) :
    heyawakeDec (bitEncode i) = true ↔ WellFormed i ∧ HeyawakeFeasible i := by
  simp [heyawakeDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : heyawakeDec [true] = false := by
  have h : bitDecode (α := HeyawakeInstance) [true] = none := rfl
  simp [heyawakeDec, h]

/-- A single row of three cells forming one room numbered `1`: painting the left cell leaves the
two white cells connected, and no white line crosses three rooms. -/
example : heyawakeDec (bitEncode (([[0, 0, 0]], [(true, 1)]) : HeyawakeInstance)) = true := by
  refine (accepts_encoding _).2 ⟨?_, fun r c => decide (r = 0 ∧ c = 0), ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide,
      fun k hk => ⟨0, by decide, 0, by decide, ?_⟩, ?_⟩
    · have hk : k < 1 := hk
      simp [roomOf]
      omega
    · intro r₁ h₁ c₁ h₂ r₂ _ c₂ _ _ r h₅ c h₆ _ _ _ _
      have : r₁ < 1 := h₁
      have : c₁ < 3 := h₂
      have : r < 1 := h₅
      have : c < 3 := h₆
      have hz : ∀ r < 1, ∀ c < 3, roomOf ([[0, 0, 0]], [(true, 1)]) r c = 0 := by decide
      rw [hz r (by omega) c (by omega), hz r₁ (by omega) c₁ (by omega)]
  unfold Solves gridGraph
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro r hr c₁ c₂ c₃ h₁₂ h₂₃ h₃ hw
    have hr : r < 1 := hr
    have h₃ : c₃ < 3 := h₃
    have := hw 0 (by omega) (by omega)
    simp at this
    omega
  · intro c _ r₁ r₂ r₃ h₁₂ h₂₃ h₃
    have h₃ : r₃ < 1 := h₃
    omega

/-- Two adjacent cells forming one room numbered `2`: both cells would be painted, but painted
cells never share a side. -/
example : heyawakeDec (bitEncode (([[0, 0]], [(true, 2)]) : HeyawakeInstance)) = false := by
  have h : ¬ HeyawakeFeasible ([[0, 0]], [(true, 2)]) := by
    rintro ⟨p, sep, -, count, -⟩
    have hc := count 0 (by decide) (by decide)
    have hs := (sep 0 (by decide) 0 (by decide))
    have hbox : Finset.range (rows ([[0, 0]], [(true, 2)])) ×ˢ
        Finset.range (cols ([[0, 0]], [(true, 2)])) = {(0, 0), (0, 1)} := by decide
    rw [hbox] at hc
    cases h₀ : p 0 0 <;> cases h₁ : p 0 1 <;>
      simp [Finset.filter_insert, Finset.filter_singleton, roomOf, h₀, h₁, rows, cols] at hc hs
  simpa [heyawakeDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.Heyawake
