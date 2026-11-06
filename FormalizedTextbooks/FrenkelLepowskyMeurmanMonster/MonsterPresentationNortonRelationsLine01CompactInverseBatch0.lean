/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A bounded kernel batch for the actual first-line inverse compact coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactColumnData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactColumnInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Evaluate only the proved bitwise formula of the actual sixty-four-term operator.
/-- Batch 0 of the full actual inverse numerator coefficient checks. -/
theorem monsterNortonLine01CompactInverse_coefficient_batch0 (k : Fin 4) (p : Fin 128) :
    monsterNortonUCompactInverseNumerator
      (monsterNortonLine01CompactInputVector ⟨0 + k.val, by omega⟩)
      (monsterNortonLine01CompactOutputLabel p) =
        monsterNortonLine01CompactOutputCoefficient ⟨0 + k.val, by omega⟩ p := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert k p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
