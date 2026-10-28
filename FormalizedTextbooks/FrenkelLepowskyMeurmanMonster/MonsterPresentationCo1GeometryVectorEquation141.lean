/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLine141
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 141 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation141 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow141) = 0 := by
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [141, 155, 165] = 0 := by
    change monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint141 +
      (monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint155 +
        (monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint165 + 0)) = 0
    simpa only [add_zero, add_assoc] using
      monsterCo1GeometryUniversalPoint_line _ _ _ monsterCo1GeometryVectorLine141
  have hc : monsterCo1GeometryVectorRowNormalize [141, 155, 165] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow141) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
