/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiGaussianPhase

/-! The exact preferred short phase is evaluated without constructing intermediate Gaussian Q
images. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Both original C quadratics, both genuine grey quadratics and the actual correction character. -/
def generatedSixthXiShortFastPhase (a s : GriessShortIndex) : ZMod 2 :=
  monsterMonomialQuadratic (representativeMatrix (generatedSixthPermutationProfilePhaseRows 1))
      (spinTranslation (griessShortQ a)) +
    xiGrayQuadratic (xiGrayGammaProjection (griessShortQ a)) +
    xiGrayQuadratic (xiGrayGammaProjection (griessShortQ a) + xiGrayGProjection (griessShortQ a)) +
    monsterMonomialQuadratic
      (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1))
      (spinTranslation (griessShortQ s)) +
    spinDot (golayLabelCoefficients 135) (spinTranslation (griessShortQ s)) +
    spinDot (golayLabelCoefficients 538) (spinModulation (griessShortQ s))

/-- The faster expression equals the full original preferred phase for all actual short labels. -/
theorem generatedSixth_xi_short_fast_phase (a s : GriessShortIndex) :
    generatedSixthXiShortFastPhase a s = generatedSixthXiShortPhase a s := by
  have hc : generatedSixthGeneratorCorrection 4 = generatedAxisFourthQFromSpin
      (golayLabelCoefficients 538) (golayLabelCoefficients 135) 0 := rfl
  unfold generatedSixthXiShortPhase generatedSixthXiRawShortPhase generatedSixthXiShortFastPhase
  rw [generatedSixth_xi_gaussian_coefficient, griessShortQ_coeff, zero_add,
    generatedFourthQShortBasis_character, hc,
    generatedAxisFourthQFromSpin_translation, generatedAxisFourthQFromSpin_modulation]
  ring

/-- Actual intermediate and final labels give the whole corrected short action via the faster
phase. -/
theorem generatedSixth_xi_short_fast_operator (r a s : GriessShortIndex)
    (ha : griessShortPermutation leechRootedA2SixthXiTransportFiber.val.2 r = a)
    (hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s)
    (X : GriessShortIndex → ℝ) :
    localShortOperator (generatedSixthCorrectedGenerator 4) X s =
      qSign (generatedSixthXiShortFastPhase a s) * X r := by
  rw [generatedSixth_xi_short_fast_phase]
  exact generatedSixth_xi_short_operator r a s ha hs X

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
