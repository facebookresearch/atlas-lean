/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket02PhaseData

/-! The checked family and physical characters give the full actual preferred-Q phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every finite source character is the actual full short-coordinate conjugation phase. -/
theorem generatedFifthSignShortPacket02_source_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthSignCachedShortPhase (sourceQCode (generatedFifthSignCode 2) 0)
      (Sum.inr (j, e)) = generatedFifthSignShortPacket02Source j e := by
  have ho : spinDot (spinModulation (sourceQCode (generatedFifthSignCode 2) 0))
      (Pi.single 11 1) = 0 := by
    rw [sourceQCode_modulation, ← sourceWordTheta_eq_polynomial]
    exact sourceWordTheta_dot_omega _
  rw [generatedFifth_sign_short_phase_formula _ _ (sourceQCode_translation _ _) ho,
    sourceQCode_modulation, ← sourceWordTheta_eq_polynomial,
    generatedFifthSignShortPacket02_source_constant,
    generatedFifthSignShortPacket02_negative_character]
  linear_combination CharTwo.add_self_eq_zero (generatedFifthSignShortPacket02Source j 0)

/-- Every finite correction character is the actual full conjugation phase of its correcting Q. -/
theorem generatedFifthSignShortPacket02_correction_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthSignCachedShortPhase (generatedFifthSignCorrection 2)
      (Sum.inr (j, e)) = generatedFifthSignShortPacket02Correction j e := by
  have ht : spinTranslation (generatedFifthSignCorrection 2) =
      golayLabelCoefficients (generatedFifthSignCode 2) :=
    generatedAxisFourthQFromSpin_translation _ _ _
  rw [generatedFifth_sign_short_phase_formula _ _ ht (generatedFifth_sign_correction_omega 2)]
  change generatedFifthSignFamilyConstant (generatedFifthSignCode 2)
    (spinModulation (generatedAxisFourthQFromSpin _ _ _)) j + _ = _
  rw [generatedAxisFourthQFromSpin_modulation, generatedFifthSignShortPacket02_correction_constant,
    generatedFifthSignShortPacket02_negative_character,
    generatedFifthSignShortPacket02_row_relation j e]
  abel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
