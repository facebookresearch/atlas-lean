/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthPairPhaseCache

/-! Exact integer numerators for the original fourth-axis short coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual pair coordinate numerator at common denominator sixteen. -/
def generatedFourthLiftShortPairNumerator (s : Fin 2) (a b : Fin 24) : ℤ :=
  (if s = 0 then generatedFourthQShortBasisProjectionNumerator a b else
    -generatedFourthQShortBasisProjectionNumerator a b) +
      if (a, b) = (8, 11) then 8 else 0

/-- Every actual pair coefficient retains both its projector and preferred short contributions. -/
theorem generatedFourth_lift_short_pair_numerator (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedFourthAxis).2.1 (Sum.inl (s, p)) =
      (generatedFourthLiftShortPairNumerator s
        (griessCoordinatePair p).1 (griessCoordinatePair p).2 : ℝ) / 16 := by
  have hs : s = 0 ∨ s = 1 := by
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hs with rfl | rfl
  · rw [generatedFourthAxis_local_expression, generatedFourthQShortBasis_triality_pair_minus,
      generatedFourthQShortBasis_middle_matrix, generatedFourth_local_short,
      generatedFourth_transported_pair_coordinate, generatedFourth_transported_pair_coordinate,
      generatedFourth_pair_phase_zero]
    by_cases h : griessCoordinatePair p = (8, 11)
    · simp [generatedFourthLiftShortPairNumerator, h]
      ring
    · simp [generatedFourthLiftShortPairNumerator, h]
  · rw [generatedFourthAxis_local_expression, generatedFourthQShortBasis_triality_pair_plus,
      generatedFourthQShortBasis_middle_matrix, generatedFourth_local_short,
      generatedFourth_transported_pair_coordinate, generatedFourth_transported_pair_coordinate,
      generatedFourth_pair_phase_zero]
    by_cases h : griessCoordinatePair p = (8, 11)
    · simp [generatedFourthLiftShortPairNumerator, h]
      ring
    · simp [generatedFourthLiftShortPairNumerator, h]
      ring

/-- The actual listed-octad numerator at the same common denominator sixteen. -/
def generatedFourthLiftShortOctadNumerator (j : Fin 63) (e : Fin 64) : ℤ :=
  2 * generatedFourthQShortBasisOctadNumerator (generatedFourthEvenRootCode j) e

/-- The genuine listed octad coefficient has exactly its integer common-denominator numerator. -/
theorem generatedFourth_lift_short_octad_numerator (j : Fin 63) (e : Fin 64) :
    (griessConwayEncode generatedFourthAxis).2.1
      (Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e))) =
        (generatedFourthLiftShortOctadNumerator j e : ℝ) / 16 := by
  rw [generatedFourthQShortBasis_octad_coordinate, generatedFourthEvenRootOctad_label]
  simp only [generatedFourthLiftShortOctadNumerator, Int.cast_mul, Int.cast_ofNat]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
