/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortSourcePacked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! A complete independent interval of original signed short-source coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
-- Check every original coordinate in this complete bounded source interval.
/-- Every original signed short-source numerator agrees with the complete integer cache. -/
theorem generatedRootEight_positive_final_short_source_packet_27_block_01 : ∀ u : Fin 256,
    generatedRootEightPositiveFinalShortNumerator
      (generatedNinthLowerSpinShortIndex ⟨27904 + u.val, by omega⟩) =
      generatedRootEightPositiveFinalShortCachedNumerator
        (generatedNinthLowerSpinShortIndex ⟨27904 + u.val, by omega⟩) := by
  simp_rw [← generatedRootEight_positive_final_short_packed_actual]
  unfold generatedRootEightPositiveFinalShortPackedNumerator
  simp only [← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
