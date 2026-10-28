/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact E7 generator bounds for one chronological transporter-prefix block. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7Check

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The kernel checks literal E7 raw instructions and separates the last finite padding positions.
/-- Every actual transporter instruction in block 07 uses only E7 source generators. -/
theorem y322TransportE7Allowed07 (i : Fin 1024) :
    y322TransportE7AllowedAt (7168 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
