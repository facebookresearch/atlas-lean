/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator

/-! Exact pair-source Q coordinates give the original Xi phase and complete short numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Executable full preferred phase, retaining the original C shear and Gaussian quadratics. -/
def generatedSixthXiPairExecutablePhase (j : Fin 552) : ZMod 2 :=
  let q := generatedSixthCImage (generatedSixthXiPackedQ (generatedSixthXiPairSourceQ j))
  let s := generatedSixthXiPackedQ (generatedSixthXiPairOutputQ j)
  toAdd q.coeff + xiGrayQuadratic (xiGrayGammaProjection q) +
    xiGrayQuadratic (xiGrayGammaProjection q + xiGrayGProjection q) +
    monsterMonomialQuadratic
      (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1))
      (spinTranslation s) +
    spinDot (golayLabelCoefficients 135) (spinTranslation s) +
    spinDot (golayLabelCoefficients 538) (spinModulation s)

/-- The executable preferred source numerator uses the original sorted physical pair. -/
def generatedSixthXiPairInputNumerator (j : Fin 552) : ℤ :=
  let x := generatedSixthXiPairSourceCoordinates j
  generatedSixthMonomialPairNumerator x.1 x.2.1 x.2.2

/-- The executable output numerator is the full original pair or actual cached octad sum. -/
def generatedSixthXiPairOutputNumerator (j : Fin 552) : ℤ :=
  match generatedSixthXiPairOutputAddress j with
  | Sum.inl x => generatedSixthMonomialPairNumerator x.1 x.2.1 x.2.2
  | Sum.inr (f, e) => generatedSixthFinalOctadCachedNumerator f e

/-- Once both true preferred lifts are checked, executable phase equals original full phase. -/
theorem generatedSixth_xi_pair_phase_soundness (j : Fin 552)
    (hi : generatedSixthXiShortIntegerQ (generatedSixthXiPairInputIntegral j) =
      generatedSixthXiPackedQ (generatedSixthXiPairSourceQ j))
    (ho : generatedSixthXiShortIntegerQ (generatedSixthXiPairOutputIntegral j) =
      generatedSixthXiPackedQ (generatedSixthXiPairOutputQ j)) :
    generatedSixthXiShortDirectPhase (generatedSixthXiPairInput j)
      (generatedSixthXiPairOutput j) = generatedSixthXiPairExecutablePhase j := by
  have hqi := (generatedSixth_xi_short_integer_Q _ _
    (generatedSixth_xi_pair_input_integral j)).trans hi
  have hqo := (generatedSixth_xi_short_integer_Q _ _
    (generatedSixth_xi_pair_output_integral j)).trans ho
  have hc : generatedSixthGeneratorCorrection 4 = generatedAxisFourthQFromSpin
      (golayLabelCoefficients 538) (golayLabelCoefficients 135) 0 := rfl
  unfold generatedSixthXiShortDirectPhase generatedSixthXiPairExecutablePhase
  rw [generatedFourthQShortBasis_character, hc,
    generatedAxisFourthQFromSpin_translation, generatedAxisFourthQFromSpin_modulation,
    hqi, hqo]
  ring

/-- A sorted coordinate pair gives the exact original preferred numerator. -/
theorem generatedSixth_xi_pair_short_numerator (x : Fin 2 × Fin 24 × Fin 24)
    (hx : x.2.1 < x.2.2) :
    generatedSixthFinalShortNumerator (generatedSixthXiPairShort x) =
      generatedSixthMonomialPairNumerator x.1 x.2.1 x.2.2 := by
  have hn : x.2.1 ≠ x.2.2 := ne_of_lt hx
  rw [generatedSixthXiPairShort, dite_eq_left hn]
  simp only [generatedSixthFinalShortNumerator,
    generatedSixthFinalPairNumerator, griessPairIndex_coordinates, hx, ite_true,
    generatedSixthMonomialPairNumerator, min_eq_left (le_of_lt hx),
    max_eq_right (le_of_lt hx)]

/-- The executable source numerator is the complete actual preferred coefficient numerator. -/
theorem generatedSixth_xi_pair_input_numerator (j : Fin 552) :
    generatedSixthFinalShortNumerator (generatedSixthXiPairInput j) =
      generatedSixthXiPairInputNumerator j :=
  generatedSixth_xi_pair_short_numerator _ (generatedSixth_xi_pair_source_ordered j)

/-- The executable output numerator is the complete actual preferred coefficient numerator. -/
theorem generatedSixth_xi_pair_output_numerator (j : Fin 552) :
    generatedSixthFinalShortNumerator (generatedSixthXiPairOutput j) =
      generatedSixthXiPairOutputNumerator j := by
  unfold generatedSixthXiPairOutput generatedSixthXiPairOutputNumerator
  cases he : generatedSixthXiPairOutputAddress j with
  | inl x =>
    apply generatedSixth_xi_pair_short_numerator x
    simpa only [he] using generatedSixth_xi_pair_output_ordered j
  | inr x =>
    obtain ⟨f, e⟩ := x
    simp only [generatedSixthFinalShortNumerator, generatedSixth_final_octad_cache_label]
    exact (generatedSixth_final_octad_cached_numerator f e).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
