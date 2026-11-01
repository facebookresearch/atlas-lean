/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortPhaseFast

/-! The original full Xi phase needs only the actual source and output preferred labels. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original C image and both original Gaussian terms retain the full central phase. -/
def generatedSixthXiShortDirectPhase (r s : GriessShortIndex) : ZMod 2 :=
  let q := generatedSixthCImage (griessShortQ r)
  toAdd q.coeff + xiGrayQuadratic (xiGrayGammaProjection q) +
    xiGrayQuadratic (xiGrayGammaProjection q + xiGrayGProjection q) +
    monsterMonomialQuadratic
      (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1))
      (spinTranslation (griessShortQ s)) +
    toAdd (localAxisQPhase s (generatedSixthGeneratorCorrection 4))

/-- Actual output-line recognition alone identifies the entire original corrected Xi phase. -/
theorem generatedSixth_xi_short_direct_phase (r s : GriessShortIndex)
    (hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s) :
    localShortPhase (generatedSixthCorrectedGenerator 4) r =
      generatedSixthXiShortDirectPhase r s := by
  let C := leechRootedA2SixthXiTransportFiber
  let q := generatedSixthCImage (griessShortQ r)
  let qx := spinConjugation xiSpinHolomorph q
  have hI : representativeSpinCertificate C.val.1⁻¹
      (representativeMatrix (generatedSixthPermutationProfileInverseCoordinateRows 1))
      (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1)) :=
    generatedSixth_permutation_profile_inverse_spin 1
  have he : spinConjugation (generatedSixthRawGenerator 4).val.1 (griessShortQ r) =
      spinConjugation C.val.1⁻¹ qx := by
    change spinConjugation (C.val.1⁻¹ * xiSpinHolomorph * C.val.1) _ = _
    rw [map_mul, map_mul]
    change spinConjugation C.val.1⁻¹
      (spinConjugation xiSpinHolomorph (spinConjugation C.val.1 (griessShortQ r))) = _
    rw [generatedSixth_C_conjugation]
  have ht : spinTranslation (spinConjugation C.val.1⁻¹ qx) =
      spinTranslation (griessShortQ s) := by
    rw [← he, generatedSixth_short_image_translation, hs]
  have hi := generatedFifth_monomial_conjugation_coefficient C.val.1⁻¹ _ _ hI qx
  rw [ht] at hi
  have hc : localShortPhase (generatedSixthRawGenerator 4) r =
      toAdd q.coeff + xiGrayQuadratic (xiGrayGammaProjection q) +
        xiGrayQuadratic (xiGrayGammaProjection q + xiGrayGProjection q) +
        monsterMonomialQuadratic
          (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1))
          (spinTranslation (griessShortQ s)) := by
    change toAdd (spinConjugation (generatedSixthRawGenerator 4).val.1
      (griessShortQ r)).coeff = _
    rw [he, hi]
    dsimp only [qx]
    rw [generatedSixth_xi_conjugation_coefficient]
  rw [generatedSixthCorrectedGenerator, localShortPhase_mul, hc, hs,
    localAxisQPhase_eq_short_phase]
  rfl

/-- Actual source/output labels give the genuine corrected Xi short operator. -/
theorem generatedSixth_xi_short_direct_operator (r s : GriessShortIndex)
    (hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s)
    (X : GriessShortIndex → ℝ) :
    localShortOperator (generatedSixthCorrectedGenerator 4) X s =
      qSign (generatedSixthXiShortDirectPhase r s) * X r := by
  have hc : griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r = s := by
    rw [generatedSixth_corrected_generator_spatial]
    exact hs
  rw [← hc, localShortOperator_image, hc, generatedSixth_xi_short_direct_phase r s hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
