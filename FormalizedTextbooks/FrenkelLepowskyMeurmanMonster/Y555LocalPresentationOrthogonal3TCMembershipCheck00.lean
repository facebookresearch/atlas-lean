/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact initial block of finite source root-transport fingerprints. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCMembershipCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Each actual finite matrix fingerprint and sorted-label condition is checked separately.
/-- All 31-point fingerprints and exact sorted labels in this source block are checked. -/
theorem y322Orthogonal3TCMembershipCheck00 (i : Fin 32) :
    y322Orthogonal3TCMembershipCheckAt i.val := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
