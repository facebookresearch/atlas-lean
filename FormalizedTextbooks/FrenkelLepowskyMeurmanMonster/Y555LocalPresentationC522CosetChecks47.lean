/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite replay of the original-source right-coset steps in this interval. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetProgram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Each literal context and chronological source boundary is verified by the unchanged checker.
/-- Every claimed right-coset step in this exact finite interval passes the literal checker. -/
theorem y522CosetChecks47 (j : Fin 128) :
    y522CosetCheckAt ⟨6016 + j.val, by omega⟩ := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
