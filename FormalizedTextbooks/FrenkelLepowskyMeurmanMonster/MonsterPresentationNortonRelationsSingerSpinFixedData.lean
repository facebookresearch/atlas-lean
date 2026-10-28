/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite invariance certificate for the exact Norton fixed vector under the Singer lift. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check all 4096 actual integer coefficients after the source code relabeling.
/-- The frozen nonzero Norton fixed vector is invariant under the exact source relabeling. -/
theorem monsterNortonSinger_fixed_state_certificate : ∀ n : Fin 4096,
    monsterNortonFixedState 0
      (nortonUIntegerLabel (monsterNortonSingerCode 0 (golayLabelCoefficients n))) =
      monsterNortonFixedState 0 n := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
