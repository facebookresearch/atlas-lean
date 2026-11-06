/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadPhaseSoundness

/-! Exact entire original preferred-Q phase at an actual odd-short output. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual odd output retains the quadratic, theta, modulation and coordinate sign terms. -/
theorem generatedSixth_monomial_odd_phase_at_output (k : Fin 4) (r : GriessShortIndex)
    (d : Fin 2048) (j : Fin 24)
    (hs : griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r =
      Sum.inr (Sum.inr (d, j))) :
    localShortPhase (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)) r =
      monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
        (golayLabelCoefficients ⟨d.val, by omega⟩) +
      spinDot (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k))
        (sourceWordTheta ⟨d.val, by omega⟩) +
      spinDot (golayLabelCoefficients (generatedSixthMonomialMaskModulation k))
        (golayLabelCoefficients ⟨d.val, by omega⟩) +
      golayEncoder (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k)) j := by
  rw [generatedSixth_monomial_short_phase_at_output k r _ hs,
    generatedFourthQShortBasis_character, griessOdd_translation, griessOdd_modulation,
    generatedSixth_monomial_phase_smul_omega,
    spinDot_add_right, spinDot_add_right, generatedSixth_monomial_octad_omega_dot, add_zero,
    generatedSixth_monomial_correction_translation,
    generatedSixth_monomial_correction_modulation]
  have hc (u : SpinIndex) :
      spinDot u (fun a => (golayGeneratorBit a j : ZMod 2)) = golayEncoder u j := rfl
  rw [hc]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
