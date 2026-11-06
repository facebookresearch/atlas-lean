/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignShortPacket03Data
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
theorem generatedFifthSignShortPacket03_source_constant :
    ∀ j : Fin 56,
    generatedFifthSignFamilyConstant (generatedFifthSignCode 3)
      (sourceWordTheta (generatedFifthSignCode 3)) j =
        generatedFifthSignShortPacket03Source j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check the literal modulation against all 56 actual family constants.
/-- The correcting Q constant agrees with its zero-sign coordinate. -/
theorem generatedFifthSignShortPacket03_correction_constant :
    ∀ j : Fin 56,
    generatedFifthSignFamilyConstant (generatedFifthSignCode 3)
      (golayLabelCoefficients (generatedFifthSignModulation 3)) j =
        generatedFifthSignShortPacket03Correction j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- This is only the physical 24-coordinate character, not a repeated Q reconstruction.
/-- Every actual physical negative-position character has the displayed signed row. -/
theorem generatedFifthSignShortPacket03_negative_character :
    ∀ j : Fin 56, ∀ e : Fin 64,
    generatedFifthSignNegativeCharacter (generatedFifthSignCode 3) j e =
      generatedFifthSignShortPacket03Source j e + generatedFifthSignShortPacket03Source j 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
-- Compare the two literal finite character rows.
/-- Source and correction rows differ by precisely their family constants. -/
theorem generatedFifthSignShortPacket03_row_relation :
    ∀ j : Fin 56, ∀ e : Fin 64,
    generatedFifthSignShortPacket03Correction j e = generatedFifthSignShortPacket03Source j e +
      generatedFifthSignShortPacket03Source j 0 +
        generatedFifthSignShortPacket03Correction j 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
