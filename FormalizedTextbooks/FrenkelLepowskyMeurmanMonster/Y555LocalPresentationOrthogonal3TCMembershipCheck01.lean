/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact bounded source root-transport fingerprints and sorted-label certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCMembershipCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Each finite matrix fingerprint and its exact sorted-label conditions are checked separately.
/-- All source fingerprints and exact sorted-label conditions in this bounded block are checked. -/
theorem y322Orthogonal3TCMembershipCheck01 (i : Fin 32) :
    y322Orthogonal3TCMembershipCheckAt (32 + i.val) := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
