/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact binding of every H definition to original-source E8 certificate boundaries. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayHRuleData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- This finite check binds all six hundred twenty literal definitions to their proved word boundaries.
/-- Each H operation matches the exact input and output of its original-source certificate. -/
theorem y431AuxReplayHRule_checked (i : Fin 620) : y431AuxReplayHRuleChecked i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
