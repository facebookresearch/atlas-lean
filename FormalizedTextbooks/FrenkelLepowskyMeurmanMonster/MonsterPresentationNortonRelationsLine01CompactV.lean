/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Norton v turns the compact output high/low symmetry into antisymmetry. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQIntegerSparse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- This is a complete twelve-bit check of the genuine Norton v translation.
/-- Actual Norton v translation commutes with the high/low spin-label interchange. -/
theorem monsterNortonLine01CompactV_translation (n : Fin 4096) :
    nortonUIntegerLabel (golayLabelCoefficients (monsterNortonLine01CompactHighFlip n) +
      spinTranslation y555NortonVQ) =
        monsterNortonLine01CompactHighFlip (nortonUIntegerLabel
          (golayLabelCoefficients n + spinTranslation y555NortonVQ)) := by
  revert n
  decide +kernel

set_option maxHeartbeats 16000000 in
-- The actual central phase and modulation are retained in all 4096 checks.
/-- The genuine Norton v phase reverses between every low and high spin label. -/
theorem monsterNortonLine01CompactV_phase (n : Fin 4096) :
    nortonUIntegerSign (spinPhase y555NortonVQ
      (golayLabelCoefficients (monsterNortonLine01CompactHighFlip n))) =
        -nortonUIntegerSign (spinPhase y555NortonVQ (golayLabelCoefficients n)) := by
  revert n
  decide +kernel

/-- The next actual Norton v action makes the complete compact output vector antisymmetric. -/
theorem monsterNortonLine01CompactV_output_high (k : Fin 16) (n : Fin 4096) :
    nortonUIntegerQ y555NortonVQ (monsterNortonLine01CompactOutputVector k)
      (monsterNortonLine01CompactHighFlip n) =
        -nortonUIntegerQ y555NortonVQ (monsterNortonLine01CompactOutputVector k) n := by
  simp only [nortonUIntegerQ, monsterNortonLine01CompactV_translation,
    monsterNortonLine01CompactV_phase, monsterNortonLine01CompactOutputVector_high,
    neg_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
