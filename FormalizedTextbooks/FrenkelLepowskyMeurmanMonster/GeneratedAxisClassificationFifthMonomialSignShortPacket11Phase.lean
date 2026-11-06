/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket11PhaseData

/-! The checked family and physical characters give the full actual preferred-Q phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every finite source character is the actual full short-coordinate conjugation phase. -/
theorem generatedFifthSignShortPacket11_source_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthSignCachedShortPhase (sourceQCode (generatedFifthSignCode 11) 0)
      (Sum.inr (j, e)) = generatedFifthSignShortPacket11Source j e := by
  have ho : spinDot (spinModulation (sourceQCode (generatedFifthSignCode 11) 0))
      (Pi.single 11 1) = 0 := by
    rw [sourceQCode_modulation, ← sourceWordTheta_eq_polynomial]
    exact sourceWordTheta_dot_omega _
  rw [generatedFifth_sign_short_phase_formula _ _ (sourceQCode_translation _ _) ho,
    sourceQCode_modulation, ← sourceWordTheta_eq_polynomial,
    generatedFifthSignShortPacket11_source_constant,
    generatedFifthSignShortPacket11_negative_character]
  linear_combination CharTwo.add_self_eq_zero (generatedFifthSignShortPacket11Source j 0)

/-- Every finite correction character is the actual full conjugation phase of its correcting Q. -/
theorem generatedFifthSignShortPacket11_correction_phase (j : Fin 56) (e : Fin 64) :
    generatedFifthSignCachedShortPhase (generatedFifthSignCorrection 11)
      (Sum.inr (j, e)) = generatedFifthSignShortPacket11Correction j e := by
  have ht : spinTranslation (generatedFifthSignCorrection 11) =
      golayLabelCoefficients (generatedFifthSignCode 11) :=
    generatedAxisFourthQFromSpin_translation _ _ _
  rw [generatedFifth_sign_short_phase_formula _ _ ht (generatedFifth_sign_correction_omega 11)]
  change generatedFifthSignFamilyConstant (generatedFifthSignCode 11)
    (spinModulation (generatedAxisFourthQFromSpin _ _ _)) j + _ = _
  rw [generatedAxisFourthQFromSpin_modulation, generatedFifthSignShortPacket11_correction_constant,
    generatedFifthSignShortPacket11_negative_character,
    generatedFifthSignShortPacket11_row_relation j e]
  abel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
