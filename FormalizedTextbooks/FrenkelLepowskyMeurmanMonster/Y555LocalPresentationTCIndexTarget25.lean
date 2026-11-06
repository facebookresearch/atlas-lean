/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal original-source finite transition target bindings. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexTargetCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Exact free cancellation compares the named finite transition with its checked source claim.
/-- Every transition in target block 25 has exactly its representative-generator spelling. -/
theorem y322TCIndexTarget25 (i : Fin 256) :
    y322TCIndexTargetCheckAt (6400 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
