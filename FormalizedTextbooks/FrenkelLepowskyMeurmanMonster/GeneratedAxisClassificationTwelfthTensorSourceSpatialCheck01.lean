/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSpatialData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Whole original source words must be evaluated at every physical coordinate of the eight factors.
/-- Each complete actual physical stage has every original coordinate certified. -/
theorem generatedTwelfth_tensor_source_spatial_stage_check01 : ∀ (r : Fin 8) (i : Fin 24),
    generatedTwelfthTensorSourceStageSpatial 9 1
        (generatedTwelfthTensorSourceSpatialNumerator 1 r) i =
      generatedTwelfthTensorSourceSpatialNumerator 2 r i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
