/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket10Data
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
theorem generatedFifthSignShortPacket10_source_constant :
    ∀ j : Fin 56,
    generatedFifthSignFamilyConstant (generatedFifthSignCode 10)
      (sourceWordTheta (generatedFifthSignCode 10)) j =
        generatedFifthSignShortPacket10Source j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the literal modulation against all 56 actual family constants.
/-- The correcting Q constant agrees with its zero-sign coordinate. -/
theorem generatedFifthSignShortPacket10_correction_constant :
    ∀ j : Fin 56,
    generatedFifthSignFamilyConstant (generatedFifthSignCode 10)
      (golayLabelCoefficients (generatedFifthSignModulation 10)) j =
        generatedFifthSignShortPacket10Correction j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Verify only the eight normalized coordinates of each genuine octad character.
/-- The actual code intersection has the displayed original Walsh label. -/
theorem generatedFifthSignShortPacket10_physical_character_bits :
    ∀ j : Fin 56, ∀ z : Fin 8,
    trialityBinaryBit (generatedFifthSignShortPacket10Character j) z =
      golayBooleanCast ((golayEncodedMask 1024).testBit
        (generatedFifthEvenRootCoordinates j z).val) +
      golayBooleanCast ((golayEncodedMask 1024).testBit
        (generatedFifthEvenRootCoordinates j 7).val) := by
  decide +kernel

/-- The genuine original Walsh identity determines every physical negative-position phase. -/
theorem generatedFifthSignShortPacket10_negative_character (j : Fin 56) (e : Fin 64) :
    generatedFifthSignNegativeCharacter (generatedFifthSignCode 10) j e =
      generatedFifthSignShortPacket10Source j e + generatedFifthSignShortPacket10Source j 0 := by
  have hb := generatedFifthSignShortPacket10_physical_character_bits j
  have hs := generatedFifthSignShortPacket10_source_character j
  rw [show generatedFifthSignCode 10 = (1024 : Fin 4096) by decide +kernel]
  apply generatedFifth_sign_negative_character_of_row (⟨1024, by decide⟩ : Fin 2048) j
      (generatedFifthSignShortPacket10Character j) (generatedFifthSignShortPacket10Source j)
      hb (by simpa only [generatedFifthSignShortPacket10Alpha] using hs) e

set_option maxRecDepth 10000 in
-- Compare the two literal finite character rows.
/-- Source and correction rows differ by precisely their family constants. -/
theorem generatedFifthSignShortPacket10_row_relation :
    ∀ j : Fin 56, ∀ e : Fin 64,
    generatedFifthSignShortPacket10Correction j e = generatedFifthSignShortPacket10Source j e +
      generatedFifthSignShortPacket10Source j 0 +
        generatedFifthSignShortPacket10Correction j 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
