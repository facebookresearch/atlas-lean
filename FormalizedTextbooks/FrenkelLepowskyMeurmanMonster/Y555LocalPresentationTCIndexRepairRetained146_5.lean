/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact checks of original instructions retained alongside literal replacement certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepairOriginalCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Each literal original instruction is replayed when the selector retains it.
/-- All retained original instructions in this finite block pass their unchanged checker. -/
theorem y322TCIndexRepairRetained146_5 (i : Fin 128) :
    y322TCIndexUnreplacedCheckAt (150144 + i.val) := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
