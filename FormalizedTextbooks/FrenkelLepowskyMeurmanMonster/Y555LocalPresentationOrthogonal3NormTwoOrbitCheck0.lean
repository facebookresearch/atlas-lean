/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded exact checks of the actual original-source finite norm orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3NormTwoOrbitCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- Literal source recurrences and finite coordinate norms are checked separately.
/-- This bounded block of actual source norm-orbit recurrences is kernel-checked. -/
theorem y322Orthogonal3NormTwoCheck0 (i : Fin 128) :
    y322Orthogonal3NormTwoCheckAt (0 + i.val) := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
