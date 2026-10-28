/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadComparison

/-! Executable numerators for every actual inverse-pair source coefficient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Sixteen times each actual original fifth short coefficient, including unsupported families. -/
def generatedNinthInputShortNumerator : generatedNinthInputShortLabel → ℤ
  | Sum.inl (s, p) => generatedFifthFinalPairNumerator s p.val.1 p.val.2
  | Sum.inr (Sum.inl (j, e)) =>
      if h : (generatedNinthInputOctadComparison j).val < 56 then
        generatedFifthFinalOctadNumerator ⟨(generatedNinthInputOctadComparison j).val, h⟩ e
      else 0
  | Sum.inr (Sum.inr _) => 0

/-- Every finite coefficient numerator is the actual preferred-short coefficient. -/
theorem generatedNinthInputShortNumerator_actual (r : generatedNinthInputShortLabel) :
    (griessConwayEncode generatedFifthAxis).2.1 (generatedNinthInputShortIndex r) =
      (generatedNinthInputShortNumerator r : ℝ) / 16 := by
  rcases r with ⟨s, p⟩ | (⟨j, e⟩ | ⟨d, i⟩)
  · simp only [generatedNinthInputShortIndex, generatedNinthInputShortNumerator]
    simpa only [griessPairIndex_coordinates, p.property, ite_true] using
      generatedFifth_final_pair_numerator s
        (griessPairIndex p.val.1 p.val.2 (ne_of_lt p.property))
  · simp only [generatedNinthInputShortIndex, generatedNinthInputShortNumerator]
    split
    · rename_i h
      rw [generatedNinth_input_octad_eq j h]
      exact generatedFifth_final_octad_numerator _ _
    · rename_i h
      rw [generatedNinth_input_octad_zero j e h]
      norm_num
  · simpa only [generatedNinthInputShortIndex, generatedNinthInputShortNumerator,
      Int.cast_zero, zero_div] using generatedFifth_final_odd_zero d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
