/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeneralizedInstantInsanityDefs

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedInstantInsanity

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : GeneralizedInstantInsanityInstance) :
    generalizedInstantInsanityDec (bitEncode i) = true ↔
      WellFormed i ∧ GeneralizedInstantInsanityFeasible i := by
  simp [generalizedInstantInsanityDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : generalizedInstantInsanityDec [true] = false := by
  have h : bitDecode (α := GeneralizedInstantInsanityInstance) [true] = none := rfl
  simp [generalizedInstantInsanityDec, h]

/-- Two cubes show each of two colours exactly once on a side when they show different colours
from `{0, 1}`. -/
private theorem exactlyOnce_of_ne {side : Fin 2 → ℕ} (hne : side 0 ≠ side 1) (h₀ : side 0 < 2)
    (h₁ : side 1 < 2) : ExactlyOnce 2 side := by
  intro col hcol
  have hq : ∀ q : Fin 2, q = 0 ∨ q = 1 := Fin.forall_fin_two.2 ⟨Or.inl rfl, Or.inr rfl⟩
  by_cases h : side 0 = col
  · exact ⟨0, h, fun q hq' => (hq q).resolve_right (by rintro rfl; exact hne (h.trans hq'.symm))⟩
  · exact ⟨1, by omega, fun q hq' => (hq q).resolve_left (by rintro rfl; exact h hq')⟩

/-- Two cubes with colour pairs `(0, 1)` and `(1, 0)` on every axis: with front-back axis `0` and
right-left axis `1`, each side shows both colours. -/
example : generalizedInstantInsanityDec (bitEncode ((2, [((0, 1), (0, 1), (0, 1)),
    ((1, 0), (1, 0), (1, 0))]) : GeneralizedInstantInsanityInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    fun _ => 0, fun _ => 1, fun _ => false, fun _ => false, fun _ => by simp, ?_, ?_, ?_, ?_⟩
  all_goals exact exactlyOnce_of_ne (by decide) (by decide) (by decide)

/-- Two cubes coloured `0` all over are well formed for two colours, but colour `0` shows twice
on the front and colour `1` never. -/
example : generalizedInstantInsanityDec (bitEncode ((2, [((0, 0), (0, 0), (0, 0)),
    ((0, 0), (0, 0), (0, 0))]) : GeneralizedInstantInsanityInstance)) = false := by
  have h : ¬ GeneralizedInstantInsanityFeasible
      (2, [((0, 0), (0, 0), (0, 0)), ((0, 0), (0, 0), (0, 0))]) := by
    rintro ⟨fb, lr, sf, sr, -, front, -⟩
    have zero : ∀ (q : Fin 2) (a : Fin 3) (s : Bool),
        faceColor ([((0, 0), (0, 0), (0, 0)), ((0, 0), (0, 0), (0, 0))].get q) a s = 0 := by
      decide
    obtain ⟨q, -, huniq⟩ := front 0 (by decide)
    have e₀ : (0 : Fin 2) = q := huniq 0 (zero 0 _ _)
    have e₁ : (1 : Fin 2) = q := huniq 1 (zero 1 _ _)
    exact absurd (e₀.trans e₁.symm) (by decide)
  simpa [generalizedInstantInsanityDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.GeneralizedInstantInsanity
