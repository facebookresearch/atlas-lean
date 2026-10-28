/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket00Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPhaseFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignData

/-! Genuine preferred-Q phases, split into verified family constants and physical characters. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the actual source Parker constant once for each of the 56 families.
/-- The actual source constant agrees with the zero-sign coordinate. -/
theorem generatedFifthSignShortPacket00_source_constant :
    ∀ j : Fin 56,
    generatedFifthSignFamilyConstant (generatedFifthSignCode 0)
      (sourceWordTheta (generatedFifthSignCode 0)) j =
        generatedFifthSignShortPacket00Source j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the literal modulation against all 56 actual family constants.
/-- The correcting Q constant agrees with its zero-sign coordinate. -/
theorem generatedFifthSignShortPacket00_correction_constant :
    ∀ j : Fin 56,
    generatedFifthSignFamilyConstant (generatedFifthSignCode 0)
      (golayLabelCoefficients (generatedFifthSignModulation 0)) j =
        generatedFifthSignShortPacket00Correction j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- This is only the physical 24-coordinate character, not a repeated Q reconstruction.
/-- Every actual physical negative-position character has the displayed signed row. -/
theorem generatedFifthSignShortPacket00_negative_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    generatedFifthSignNegativeCharacter (generatedFifthSignCode 0) j e =
      generatedFifthSignShortPacket00Source j e + generatedFifthSignShortPacket00Source j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
-- Compare the two literal finite character rows.
/-- Source and correction rows differ by precisely their family constants. -/
theorem generatedFifthSignShortPacket00_row_relation :
    ∀ j : Fin 56, ∀ e : Fin 64,
    generatedFifthSignShortPacket00Correction j e = generatedFifthSignShortPacket00Source j e +
      generatedFifthSignShortPacket00Source j 0 +
        generatedFifthSignShortPacket00Correction j 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
