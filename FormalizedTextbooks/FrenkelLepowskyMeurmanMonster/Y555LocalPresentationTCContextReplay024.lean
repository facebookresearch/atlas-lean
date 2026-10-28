/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal source and contextual equation replay in the original C322 presentation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Kernel reduction replays finite literal word contexts with bounded final-block padding.
/-- Every literal equation in block 024 follows from its named source or earlier equations. -/
theorem y322TCContextReplay024 (i : Fin 256) :
    y322TCContextCheckAt (6144 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
