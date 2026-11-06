/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-source contextual replay for the full local index certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Kernel reduction checks literal source equations and earlier contextual substitutions.
/-- Every actual equation in index block 102 follows from its literal source derivation. -/
theorem y322TCIndexReplay102 (i : Fin 1024) :
    y322TCIndexCheckAt (104448 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
