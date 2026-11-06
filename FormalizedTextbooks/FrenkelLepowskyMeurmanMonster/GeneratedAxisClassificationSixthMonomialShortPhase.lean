/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthCorrectedGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalAxisStabilizerPhase

/-! The actual monomial quadratic and preferred Q correction determine every true short phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The base transport identifies the actual output translation independently of central signs. -/
theorem generatedSixth_short_image_translation (f : localFiberSubgroup) (r : GriessShortIndex) :
    spinTranslation (spinConjugation f.val.1 (griessShortQ r)) =
      spinTranslation (griessShortQ (griessShortPermutation f.val.2 r)) := by
  rw [griessShortQ_image, spinTranslation_mul]
  change 0 + _ = _
  rw [zero_add]

/-- Full original signed spin certificates give the actual raw preferred-short phase. -/
theorem generatedSixth_monomial_raw_short_phase (k : Fin 4) (r : GriessShortIndex) :
    localShortPhase (generatedSixthRawGenerator (Fin.castAdd 1 k)) r =
      monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
        (spinTranslation (griessShortQ
          (griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r))) := by
  have h := generatedFifth_monomial_conjugation_coefficient
    (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.1
    (generatedSixthMonomialSpinModel k).coordinate (generatedSixthMonomialSpinModel k).phase
    (generatedSixth_monomial_raw_spin k) (griessShortQ r)
  rw [griessShortQ_coeff, zero_add, generatedSixth_short_image_translation] at h
  exact h

/-- The actual correction adds its full extraspecial character to the original raw phase. -/
theorem generatedSixth_monomial_corrected_short_phase (k : Fin 4) (r : GriessShortIndex) :
    localShortPhase (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)) r =
      monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
        (spinTranslation (griessShortQ
          (griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r))) +
      toAdd (localAxisQPhase
        (griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r)
        (generatedSixthGeneratorCorrection (Fin.castAdd 1 k))) := by
  rw [generatedSixthCorrectedGenerator, localShortPhase_mul,
    generatedSixth_monomial_raw_short_phase, localAxisQPhase_eq_short_phase]

/-- Once the genuine output label is bound, the full original preferred phase is explicit. -/
theorem generatedSixth_monomial_short_phase_at_output (k : Fin 4)
    (r s : GriessShortIndex)
    (hs : griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r = s) :
    localShortPhase (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)) r =
      monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
        (spinTranslation (griessShortQ s)) +
      toAdd (localAxisQPhase s (generatedSixthGeneratorCorrection (Fin.castAdd 1 k))) := by
  rw [generatedSixth_monomial_corrected_short_phase, hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
