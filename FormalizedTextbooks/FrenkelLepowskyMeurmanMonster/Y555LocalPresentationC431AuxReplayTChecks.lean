/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel checks of the exact literal auxiliary path definitions for the C431 trace. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplaySourceData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- This finite comparison checks all one hundred eighty explicit auxiliary path definitions.
/-- Every T operation matches the actual declared original-source path word exactly. -/
theorem y431AuxReplayTDefinition_checked (i : Fin 180) :
    y431AuxReplayTDefinitionChecked i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
