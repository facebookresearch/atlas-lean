/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSpinDataB
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceStages

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- The whole stage word is evaluated at every physical coordinate of the eight factors.
/-- The physical numerators of root-two stage 5. -/
theorem generatedFeasibleAmbientTenth_spatial_check05 : ∀ (r : Fin 8) (i : Fin 24),
    generatedTwelfthTensorSourceStageSpatial 2 5 (generatedFeasibleAmbientTenthSpatial 5 r) i =
      1 * generatedFeasibleAmbientTenthSpatial 6 r i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
