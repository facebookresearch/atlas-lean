/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact original-source contextual equation replay, chronological block 21. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayProgram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Kernel reduction checks the literal source equations and strictly earlier contextual substitutions.
/-- Every exact contextual equation in chronological block 21 passes the unchanged checker. -/
theorem y431AuxReplayChecks21 (i : Fin 128) :
    y431AuxReplayCheckAt ⟨2688 + i.val, by omega⟩ := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
