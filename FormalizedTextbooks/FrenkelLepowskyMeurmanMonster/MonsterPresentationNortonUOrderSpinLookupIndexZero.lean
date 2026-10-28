/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- An exact finite certificate for one actual Norton source factor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinLookup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Verify all 4096 displayed output labels against the actual linear or affine action.
/-- Exact finite relabeling certificate for lookup table 0. -/
theorem monsterNortonSpinIndex_0 : ∀ n : Fin 4096,
    monsterNortonSpinIndex 0 n =
      nortonUIntegerLabel (monsterSourcePermutationCode 0 (golayLabelCoefficients n)) := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
