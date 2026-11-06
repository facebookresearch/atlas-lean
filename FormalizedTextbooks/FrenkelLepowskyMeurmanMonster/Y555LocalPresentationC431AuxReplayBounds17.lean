/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite chronological and alphabet bounds for original-source replay block 17. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayData17

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The finite check unfolds the literal claimed words and every chronological reference in this block.
/-- Every literal letter and source or prior-equation reference satisfies its exact finite bound. -/
theorem y431AuxReplayBounds17 (i : Fin 128) :
    (y431AuxReplayData17 i).Allowed 810 856 (2176 + i.val) := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
