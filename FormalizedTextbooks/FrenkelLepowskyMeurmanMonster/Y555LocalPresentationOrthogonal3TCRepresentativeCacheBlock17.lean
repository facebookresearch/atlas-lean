/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite source trace-node binding certificate for representative prefix block 17. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCacheCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Literal source trace-node equality is checked on every representative label in this block.
/-- Every original source representative in finite block 17 has the exact cached prefix node. -/
theorem y322Orthogonal3TCRepresentativeCacheBlock17 (i : Fin 128) :
    y322Orthogonal3TCRepresentativeCacheCheckAt (2176 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
