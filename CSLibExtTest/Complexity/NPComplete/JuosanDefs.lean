/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.JuosanDefs

namespace MetaMathlibExt.Complexity.NPComplete.Juosan

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.Heyawake (HeyawakeInstance rows cols roomOf WellFormed)

private theorem accepts_encoding (i : HeyawakeInstance) :
    juosanDec (bitEncode i) = true ↔ WellFormed i ∧ JuosanFeasible i := by
  simp [juosanDec, bitDecode_bitEncode]

/-- A `1 × 3` grid forming one territory with the number `n`. -/
private abbrev strip (n : ℕ) : HeyawakeInstance := ([[0, 0, 0]], [(true, n)])

private theorem room_zero (r c : ℕ) : ([[0, 0, 0]].getD r []).getD c 0 = 0 := by
  rcases r with _ | r <;> rcases c with _ | _ | _ | c <;> simp

private theorem wellFormed_strip (n : ℕ) : WellFormed (strip n) := by
  have h : WellFormed ([[0, 0, 0]], [(true, 0)]) := by
    unfold WellFormed rows cols roomOf
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · intro k hk
      exact ⟨0, by decide, 0, by decide, by simp at hk; simp [hk]⟩
    · intros
      rw [room_zero, room_zero]
  exact h

/-- A lone continuation bit is a truncated instance encoding. -/
example : juosanDec [true] = false := by
  have h : bitDecode (α := HeyawakeInstance) [true] = none := rfl
  simp [juosanDec, h]

/-- The filling `− | −` has two `−` marks and one `|` mark, so the larger count is `2`, and no
three `|` marks are in a row. -/
example : juosanDec (bitEncode (strip 2)) = true := by
  apply (accepts_encoding _).2
  refine ⟨wellFormed_strip 2, fun _ c => decide (c ≠ 1), ?_, ?_, ?_⟩
  · intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    intro _
    unfold markCount rows cols roomOf
    decide
  · intro r c hr
    simp [rows] at hr
  · intro r c _ hc
    simp only [cols, List.headD_cons, List.length_cons, List.length_nil] at hc
    have hc0 : c = 0 := by omega
    subst hc0
    simp

/-- Three cells always give one mark kind at least twice, so the number `1` is unreachable. -/
example : juosanDec (bitEncode (strip 1)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, m, hnum, -, -⟩ := (accepts_encoding _).1 hacc
  have h := hnum 0 (by decide) rfl
  have hs : Finset.range (rows (strip 1)) ×ˢ Finset.range (cols (strip 1)) =
      {(0, 0), (0, 1), (0, 2)} := by decide
  simp only [markCount, hs] at h
  cases h₀ : m 0 0 <;> cases h₁ : m 0 1 <;> cases h₂ : m 0 2 <;>
    simp [Finset.filter_insert, Finset.filter_singleton, roomOf, h₀, h₁, h₂] at h

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed (strip 1) :=
  wellFormed_strip 1

end MetaMathlibExt.Complexity.NPComplete.Juosan
