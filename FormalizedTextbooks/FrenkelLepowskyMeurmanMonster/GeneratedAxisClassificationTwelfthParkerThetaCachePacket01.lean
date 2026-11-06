/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCacheData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 8000000 in
-- Check all bits of the original Parker quadratic source formula at every bounded label.
/-- Every original label in the packet retains its entire preferred-lift cocode mask. -/
theorem generatedTwelfth_parker_theta_cache_packet_01 : ∀ u : Fin 256,
    let d : Fin 4096 := ⟨1 * 256 + u.val, by omega⟩
    generatedTwelfthParkerThetaCache d = parkerThetaMask d.val := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
