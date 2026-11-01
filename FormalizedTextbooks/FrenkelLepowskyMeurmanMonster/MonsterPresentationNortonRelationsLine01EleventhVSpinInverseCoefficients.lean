/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact inverse Norton U transport of the reached rank-thirty-two spin packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhVSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactColumnInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The two original spin deltas which survive the actual inverse U step. -/
def monsterNortonLine01ThirteenthSpinVector : NortonUIntegerVector :=
  Pi.single 0 1 + Pi.single 2048 1

set_option maxHeartbeats 16000000 in
-- Check only the already proved 128-label output catalogue with the actual inverse evaluator.
/-- The exact inverse coefficients on the complete proved output catalogue. -/
theorem monsterNortonLine01EleventhVSpin_inverse_coefficients (p : Fin 128) :
    monsterNortonUCompactInverseNumerator monsterNortonLine01EleventhVSpinVector
      (monsterNortonLine01CompactOutputLabel p) =
        32 * monsterNortonLine01ThirteenthSpinVector
          (monsterNortonLine01CompactOutputLabel p) := by
  rw [monsterNortonUCompactColumnInverseNumerator_actual]
  revert p
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
