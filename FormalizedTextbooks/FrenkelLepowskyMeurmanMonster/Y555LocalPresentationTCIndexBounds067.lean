/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact source, alphabet and chronological reference bounds for local table-edge proofs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks finite literal source, letter and earlier-equation bounds with last-block padding.
/-- Every actual edge certificate in block 067 retains strict chronological bounds. -/
theorem y322TCIndexAllowed067 (i : Fin 1024) :
    y322TCIndexAllowedAt (68608 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
