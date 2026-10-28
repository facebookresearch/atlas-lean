/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQFull

/-! Complete original short support before the literal ninth local word is applied. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All signed pairs and all64 rows of the56 genuinely supported original octad families. -/
abbrev generatedNinthOriginalShortLabel := (Fin 2 × Fin 276) ⊕ (Fin 56 × Fin 64)

/-- These original source rows form a finite4136-label catalogue. -/
theorem generatedNinth_original_short_label_card :
    Fintype.card generatedNinthOriginalShortLabel = 4136 := by
  norm_num [generatedNinthOriginalShortLabel, Fintype.card_sum, Fintype.card_prod]

/-- Actual preferred source indices in the original physical short-coordinate catalogue. -/
def generatedNinthOriginalShortIndex : generatedNinthOriginalShortLabel → GriessShortIndex
  | Sum.inl r => Sum.inl r
  | Sum.inr (j, e) => Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))

/-- The executable original signed numerator, with its complete preferred-Q phase. -/
def generatedNinthOriginalShortNumerator : generatedNinthOriginalShortLabel → ℤ
  | Sum.inl (s, p) => generatedFifthFinalPairNumerator s
      (griessCoordinatePair p).1 (griessCoordinatePair p).2
  | Sum.inr (j, e) => generatedFifthFinalOctadNumerator j e

/-- Each displayed source numerator is sixteen times the corresponding actual short coefficient. -/
theorem generatedNinth_original_short_numerator_actual (a : generatedNinthOriginalShortLabel) :
    (griessConwayEncode generatedFifthAxis).2.1 (generatedNinthOriginalShortIndex a) =
      (generatedNinthOriginalShortNumerator a : ℝ) / 16 := by
  rcases a with ⟨s, p⟩ | ⟨j, e⟩
  · exact generatedFifth_final_pair_numerator s p
  · exact generatedFifth_final_octad_numerator j e

/-- Every genuinely nonzero original short row is in the displayed source catalogue. -/
theorem generatedNinth_original_short_nonzero_covered (r : GriessShortIndex)
    (hr : (griessConwayEncode generatedFifthAxis).2.1 r ≠ 0) :
    ∃ a : generatedNinthOriginalShortLabel, generatedNinthOriginalShortIndex a = r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · exact ⟨Sum.inl (s, p), rfl⟩
  · have ho : ∃ j : Fin 56, generatedFifthEvenRootOctad j = o := by
      by_contra h
      exact hr (generatedFifth_final_octad_zero o e h)
    obtain ⟨j, hj⟩ := ho
    exact ⟨Sum.inr (j, e), by simp only [generatedNinthOriginalShortIndex, hj]⟩
  · exact (hr (generatedFifth_final_odd_zero d i)).elim

/-- An original row with a nonzero actual coefficient has a nonzero signed source numerator. -/
theorem generatedNinth_original_short_numerator_ne_zero (a : generatedNinthOriginalShortLabel)
    (ha : (griessConwayEncode generatedFifthAxis).2.1 (generatedNinthOriginalShortIndex a) ≠ 0) :
    generatedNinthOriginalShortNumerator a ≠ 0 := by
  intro h
  rw [generatedNinth_original_short_numerator_actual, h, Int.cast_zero, zero_div] at ha
  exact ha rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
