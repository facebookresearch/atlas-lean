/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortFiniteData

/-! A bounded actual short-coordinate certificate for the first listed octad family. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Verify the full preferred-Q phase and original integer coefficient at each sign row.
/-- Every sign in the first genuine octad family has the certified actual target and coefficient. -/
theorem generatedFourth_lift_short_finite_profile :
    ∀ e : Fin 64, generatedFourthLiftShortFiniteMatch
      (generatedFourthLiftShortSourceQ 0 e) (generatedFourthLiftShortOctadNumerator 0 e)
        (generatedFourthLiftShortOctadTargets 0 e) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
