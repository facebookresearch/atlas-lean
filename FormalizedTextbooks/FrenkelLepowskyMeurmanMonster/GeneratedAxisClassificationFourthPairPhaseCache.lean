/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthWatermark

/-! The selected pair's genuine central phase, checked against the full original Q action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Retain all central phases of the original Xi, P0, Xi inverse action.
/-- The preferred middle pair has zero actual inverse central phase. -/
theorem generatedFourth_pair_phase_zero : generatedFourthPairPhase = 0 := by
  unfold generatedFourthPairPhase
  simp only [monsterNortonShortQ, generatedFourthPairInput,
    griessShortIntegral, griessPairIndex_coordinates,
    show (8 : Fin 24) < 11 from by decide, ite_true]
  decide +kernel

/-- The selected preferred short vector is the minus pair on coordinates eight and eleven. -/
theorem generatedFourth_flag_short_coordinates (i : Fin 24) :
    griessShortVector generatedFourthFlagShort i =
      (4 * (if i = 8 then 1 else 0) - 4 * (if i = 11 then 1 else 0)) / Real.sqrt 8 := by
  simpa only [generatedFourth_pair_phase_zero, qSign_zero, mul_one] using
    generatedFourth_flag_short_vector i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
