/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterBasisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisCharacters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthDiagonal
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact integer numerator of the middle matrix projector. -/
def generatedFourthQShortBasisProjectionNumerator (i j : Fin 24) : ℤ :=
  ∑ k : Fin 24, if Nat.testBit 0xcccc00 k.val then
    generatedFourthInverseNumerator k i * generatedFourthInverseNumerator k j else 0

/-- The literal binary character on a preferred pair for each of the seven genuine Q generators. -/
def generatedFourthQShortBasisPairPhase (i : Fin 7) (p : Fin 276) : ZMod 2 :=
  spinDot (golayLabelCoefficients (generatedFourthQAffineParameterBasisTranslationLabels i))
    (griessPairSyndrome p)

/-- Every literal basis modulation has zero bit eleven. -/
theorem generatedFourthQShortBasis_modulation_last : ∀ i : Fin 7,
    golayLabelCoefficients (generatedFourthQAffineParameterBasisModulationLabels i) 11 = 0 := by
  decide +kernel

/-- The same literal pair character evaluated on two explicit physical coordinates. -/
def generatedFourthQShortBasisPairCoordinatePhase (i : Fin 7) (a b : Fin 24) : ZMod 2 :=
  ∑ k : Fin 12,
    golayLabelCoefficients (generatedFourthQAffineParameterBasisTranslationLabels i) k *
      ((golayGeneratorBit k a : ZMod 2) + (golayGeneratorBit k b : ZMod 2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check exact pair characters on 4032 coordinate triples against 24-term projector numerators.
/-- Nontrivial coordinate characters occur only where both middle contributions are zero. -/
theorem generatedFourthQShortBasis_pair_coordinate_zero_certificate :
    ∀ i : Fin 7, ∀ a b : Fin 24,
    generatedFourthQShortBasisPairCoordinatePhase i a b ≠ 0 →
      generatedFourthQShortBasisProjectionNumerator a b = 0 ∧ (a, b) ≠ (8, 11) := by
  decide +kernel

/-- Nontrivial actual pair characters occur only where both middle contributions are zero. -/
theorem generatedFourthQShortBasis_pair_zero_certificate (i : Fin 7) (p : Fin 276)
    (h : generatedFourthQShortBasisPairPhase i p ≠ 0) :
    generatedFourthQShortBasisProjectionNumerator
      (griessCoordinatePair p).1 (griessCoordinatePair p).2 = 0 ∧
    griessCoordinatePair p ≠ (8, 11) := by
  exact generatedFourthQShortBasis_pair_coordinate_zero_certificate i
    (griessCoordinatePair p).1 (griessCoordinatePair p).2 h

/-- The seven genuine Q pair characters are exactly their literal finite binary formulas. -/
theorem generatedFourthQShortBasis_pair_character (i : Fin 7) (s : Fin 2) (p : Fin 276) :
    Multiplicative.toAdd (localAxisQPhase (Sum.inl (s, p))
      (generatedFourthQAffineParameterBasis i)) = generatedFourthQShortBasisPairPhase i p := by
  rw [generatedFourthQShortBasis_character, generatedFourthQAffineParameterBasis_literal,
    generatedAxisFourthQFromSpin_translation, generatedAxisFourthQFromSpin_modulation]
  have hs : s = 0 ∨ s = 1 := by
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hs with rfl | rfl
  · rw [griessPairMinus_modulation, griessPairMinus_translation]
    simp [generatedFourthQShortBasisPairPhase]
  · rw [griessPairPlus_modulation, griessPairPlus_translation]
    have h : spinDot
        (golayLabelCoefficients (generatedFourthQAffineParameterBasisModulationLabels i))
        (Pi.single 11 1) = 0 := by
      simp [spinDot, Pi.single_apply, generatedFourthQShortBasis_modulation_last]
    rw [h, add_zero]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
