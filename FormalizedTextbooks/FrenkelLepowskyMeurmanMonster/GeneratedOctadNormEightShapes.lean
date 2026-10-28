/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOctadSigns

/-! Actual norm-eight vectors in the coordinate E8 section have only three shapes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Support in the actual first-eight-coordinate Golay octad. -/
def generatedStandardOctadSupported (u : Fin 24 → ℤ) : Prop :=
  ∀ i : Fin 24, 8 ≤ i.val → u i = 0

/-- The sixteen exterior coordinates contribute sixteen zeros to the actual catalogue. -/
theorem generatedStandardOctad_zero_multiplicity (u : Fin 24 → ℤ)
    (hu : generatedStandardOctadSupported u) :
    16 ≤ leechNormEightMultiplicity u 0 := by
  classical
  have hc : (Finset.univ.filter (fun i : Fin 24 => 8 ≤ i.val)).card = 16 := by
    decide +kernel
  rw [← hc]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
    rw [hu i (Finset.mem_filter.mp hi).2]
    rfl⟩

/-- Only the coordinate, seven-two/one-six, and four-four shapes occur in this section. -/
theorem generatedStandardOctad_normEight_shapes (u : leechIntegral)
    (hs : leechSquareSum u.val = 64) (hu : generatedStandardOctadSupported u.val) :
    ∃ s : Fin 8, (s = 0 ∨ s = 1 ∨ s = 2) ∧
      leechNormEightMultiplicity u.val = leechNormEightShapeCounts s := by
  obtain ⟨s, he⟩ := leechNormEight_catalog u hs
  have hz := generatedStandardOctad_zero_multiplicity u.val hu
  rw [he] at hz
  fin_cases s
  · exact ⟨0, Or.inl rfl, he⟩
  · exact ⟨1, Or.inr (Or.inl rfl), he⟩
  · exact ⟨2, Or.inr (Or.inr rfl), he⟩
  all_goals norm_num [leechNormEightShapeCounts] at hz

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
