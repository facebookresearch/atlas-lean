/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel replay of every literal original-source E8 move in block 7. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431E8RewriteData07

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

-- Replaying these sixty-four-move certificates requires the literal list expressions to unfold.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- The finite check evaluates all original Coxeter conditions in this bounded block.
/-- Every proposed chunk in block 7 passes the unchanged original-source move checker. -/
theorem y431E8RewriteChecks07 (i : Fin 64) :
    y431CoxeterRun (y431E8RewriteData07 i).2.2 (y431E8RewriteData07 i).1 =
      some (y431E8RewriteData07 i).2.1 := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
