/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact earlier-reference bounds for a chronological transporter word-program block. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Every reference is checked against its own actual chronological instruction index.
/-- All 1024 source-word instruction slots in block 40 have earlier references. -/
theorem y322TransportAllowed40 (i : Fin 1024) :
    y322TransportAllowedAt (40960 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
