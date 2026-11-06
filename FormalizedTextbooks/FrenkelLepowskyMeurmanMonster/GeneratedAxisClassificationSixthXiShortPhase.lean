/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialShortPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPermutationSpinProfiles
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinHolomorph

/-! The complete original conjugated-Xi short phase has two C quadratics and the true Gaussian
image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The full original raw phase, with the actual preferred intermediate C-image label retained. -/
noncomputable def generatedSixthXiRawShortPhase (a s : GriessShortIndex) : ZMod 2 :=
  monsterMonomialQuadratic (representativeMatrix (generatedSixthPermutationProfilePhaseRows 1))
      (spinTranslation (griessShortQ a)) +
    toAdd (xiSpinGImage (xiSpinGammaImage (griessShortQ a))).coeff +
    monsterMonomialQuadratic
      (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1))
      (spinTranslation (griessShortQ s))

/-- The actual extraspecial correction adds its genuine output character to the full raw phase. -/
noncomputable def generatedSixthXiShortPhase (a s : GriessShortIndex) : ZMod 2 :=
  generatedSixthXiRawShortPhase a s +
    toAdd (localAxisQPhase s (generatedSixthGeneratorCorrection 4))

/-- Both complete original C certificates and the actual Gaussian image give the raw short phase. -/
theorem generatedSixth_xi_raw_short_phase (r a s : GriessShortIndex)
    (ha : griessShortPermutation leechRootedA2SixthXiTransportFiber.val.2 r = a)
    (hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s) :
    localShortPhase (generatedSixthRawGenerator 4) r = generatedSixthXiRawShortPhase a s := by
  let C := leechRootedA2SixthXiTransportFiber
  have hC : representativeSpinCertificate C.val.1
      (representativeMatrix (generatedSixthPermutationProfileCoordinateRows 1))
      (representativeMatrix (generatedSixthPermutationProfilePhaseRows 1)) :=
    generatedSixth_permutation_profile_spin 1
  have hI : representativeSpinCertificate C.val.1⁻¹
      (representativeMatrix (generatedSixthPermutationProfileInverseCoordinateRows 1))
      (representativeMatrix (generatedSixthPermutationProfileInversePhaseRows 1)) :=
    generatedSixth_permutation_profile_inverse_spin 1
  have hc := generatedFifth_monomial_conjugation_coefficient C.val.1 _ _ hC (griessShortQ r)
  rw [griessShortQ_coeff, zero_add, generatedSixth_short_image_translation, ha] at hc
  change localShortPhase C r = _ at hc
  let qx := spinConjugation xiSpinHolomorph (spinConjugation C.val.1 (griessShortQ r))
  have hx : qx = qCentral (localShortPhase C r) *
      xiSpinGImage (xiSpinGammaImage (griessShortQ a)) := by
    dsimp only [qx]
    rw [griessShortQ_image C r, ha, map_mul, spinConjugation_central,
      xiSpinHolomorph_conjugation]
  have he : spinConjugation (generatedSixthRawGenerator 4).val.1 (griessShortQ r) =
      spinConjugation C.val.1⁻¹ qx := by
    change spinConjugation (C.val.1⁻¹ * xiSpinHolomorph * C.val.1) _ = _
    rw [map_mul, map_mul]
    rfl
  have ht : spinTranslation (spinConjugation C.val.1⁻¹ qx) =
      spinTranslation (griessShortQ s) := by
    rw [← he, generatedSixth_short_image_translation, hs]
  have hi := generatedFifth_monomial_conjugation_coefficient C.val.1⁻¹ _ _ hI qx
  rw [ht] at hi
  change toAdd (spinConjugation (generatedSixthRawGenerator 4).val.1 (griessShortQ r)).coeff = _
  rw [he, hi, hx, qCentral_mul_coeff, hc]
  rfl

/-- The exact preferred phase of the corrected original conjugated Xi at a bound output label. -/
theorem generatedSixth_xi_short_phase (r a s : GriessShortIndex)
    (ha : griessShortPermutation leechRootedA2SixthXiTransportFiber.val.2 r = a)
    (hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s) :
    localShortPhase (generatedSixthCorrectedGenerator 4) r = generatedSixthXiShortPhase a s := by
  rw [generatedSixthCorrectedGenerator, localShortPhase_mul,
    generatedSixth_xi_raw_short_phase r a s ha hs, hs, localAxisQPhase_eq_short_phase]
  rfl

/-- Bound original labels give the exact corrected short-coordinate operator and full phase. -/
theorem generatedSixth_xi_short_operator (r a s : GriessShortIndex)
    (ha : griessShortPermutation leechRootedA2SixthXiTransportFiber.val.2 r = a)
    (hs : griessShortPermutation (generatedSixthRawGenerator 4).val.2 r = s)
    (X : GriessShortIndex → ℝ) :
    localShortOperator (generatedSixthCorrectedGenerator 4) X s =
      qSign (generatedSixthXiShortPhase a s) * X r := by
  have hc : griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r = s := by
    rw [generatedSixth_corrected_generator_spatial]
    exact hs
  rw [← hc, localShortOperator_image, hc, generatedSixth_xi_short_phase r a s ha hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
