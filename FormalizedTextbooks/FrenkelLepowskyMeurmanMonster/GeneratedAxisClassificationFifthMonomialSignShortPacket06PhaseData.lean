/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket06Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPhaseFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignPhysicalCharacter

/-! Genuine preferred-Q phases, split into verified family constants and physical characters. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the actual source Parker constant once for each of the 56 families.
/-- The actual source constant agrees with the zero-sign coordinate. -/
theorem generatedFifthSignShortPacket06_source_constant :
    ∀ j : Fin 56,
    generatedFifthSignFamilyConstant (generatedFifthSignCode 6)
      (sourceWordTheta (generatedFifthSignCode 6)) j =
        generatedFifthSignShortPacket06Source j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the literal modulation against all 56 actual family constants.
/-- The correcting Q constant agrees with its zero-sign coordinate. -/
theorem generatedFifthSignShortPacket06_correction_constant :
    ∀ j : Fin 56,
    generatedFifthSignFamilyConstant (generatedFifthSignCode 6)
      (golayLabelCoefficients (generatedFifthSignModulation 6)) j =
        generatedFifthSignShortPacket06Correction j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify only the eight normalized coordinates of each genuine octad character.
/-- The actual code intersection has the displayed original Walsh label. -/
theorem generatedFifthSignShortPacket06_physical_character_bits :
    ∀ j : Fin 56, ∀ z : Fin 8,
    trialityBinaryBit (generatedFifthSignShortPacket06Character j) z =
      golayBooleanCast ((golayEncodedMask 64).testBit
        (generatedFifthEvenRootCoordinates j z).val) +
      golayBooleanCast ((golayEncodedMask 64).testBit
        (generatedFifthEvenRootCoordinates j 7).val) := by
  decide +kernel

/-- The genuine original Walsh identity determines every physical negative-position phase. -/
theorem generatedFifthSignShortPacket06_negative_character (j : Fin 56) (e : Fin 64) :
    generatedFifthSignNegativeCharacter (generatedFifthSignCode 6) j e =
      generatedFifthSignShortPacket06Source j e + generatedFifthSignShortPacket06Source j 0 := by
  have hb := generatedFifthSignShortPacket06_physical_character_bits j
  have hs := generatedFifthSignShortPacket06_source_character j
  rw [show generatedFifthSignCode 6 = (64 : Fin 4096) by decide +kernel]
  apply generatedFifth_sign_negative_character_of_row (⟨64, by decide⟩ : Fin 2048) j
      (generatedFifthSignShortPacket06Character j) (generatedFifthSignShortPacket06Source j)
      hb (by simpa only [generatedFifthSignShortPacket06Alpha] using hs) e

set_option maxRecDepth 10000 in
-- Compare the two literal finite character rows.
/-- Source and correction rows differ by precisely their family constants. -/
theorem generatedFifthSignShortPacket06_row_relation :
    ∀ j : Fin 56, ∀ e : Fin 64,
    generatedFifthSignShortPacket06Correction j e = generatedFifthSignShortPacket06Source j e +
      generatedFifthSignShortPacket06Source j 0 +
        generatedFifthSignShortPacket06Correction j 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
