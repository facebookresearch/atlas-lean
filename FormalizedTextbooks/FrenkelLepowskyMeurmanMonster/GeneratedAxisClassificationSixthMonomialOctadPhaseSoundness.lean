/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOctadPhaseData

/-! Cached six-bit phases equal the entire original preferred-Q phase at genuine octad output. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original modulation is exactly its displayed binary label. -/
theorem generatedSixth_monomial_correction_modulation (k : Fin 4) :
    spinModulation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) =
      golayLabelCoefficients (generatedSixthMonomialMaskModulation k) := by
  fin_cases k <;> exact generatedAxisFourthQFromSpin_modulation _ _ _

/-- The even actual correction has zero phase on the octad Omega term. -/
theorem generatedSixth_monomial_octad_omega_dot (k : Fin 4) (c : ZMod 2) :
    spinDot (spinModulation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)))
      (c • Pi.single 11 1) = 0 := by
  simp only [spinDot, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one,
    generatedSixth_monomial_correction_even, zero_mul]

/-- True preferred octad output phase is the verified constant plus six sign-character bits. -/
theorem generatedSixth_monomial_octad_phase_cache (k : Fin 4) (r : GriessShortIndex)
    (f : Fin 231) (e : Fin 64)
    (hs : griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r =
      Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) :
    localShortPhase (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)) r =
      generatedSixthMonomialOctadPhase k f e := by
  rw [generatedSixth_monomial_octad_phase_at_output k r _ e hs,
    spinDot_add_right, spinDot_add_right, generatedSixth_monomial_octad_omega_dot, add_zero,
    generatedSixth_monomial_correction_translation,
    generatedSixth_monomial_correction_modulation,
    generatedSixth_monomial_mask_phase,
    generatedSixth_final_octad_cache_label,
    generatedSixth_octad_negative_character]
  simp only [generatedSixth_monomial_octad_coordinates,
    generatedSixth_monomial_octad_phase_character]
  have hb := generatedSixth_monomial_octad_phase_base k f
  unfold generatedSixthMonomialOctadPhase
  rw [← hb]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
