/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This equation follows only from original genuine lines and earlier source equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLine139
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorValues

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Check the literal sparse cancellation and retain only chronological prior source equations.
/-- Chronological source equation 139 is proved in the independently defined universal module. -/
theorem monsterCo1GeometryVectorEquation139 :
      monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue
      (monsterCo1GeometryVectorRow139) = 0 := by
  have hs : monsterCo1GeometryVectorRowEval monsterCo1GeometryVectorValue [15, 155, 163] = 0 := by
    change monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint15 +
      (monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint155 +
        (monsterCo1GeometryUniversalPoint monsterCo1GeometryVectorPoint163 + 0)) = 0
    simpa only [add_zero, add_assoc] using
      monsterCo1GeometryUniversalPoint_line _ _ _ monsterCo1GeometryVectorLine139
  have hc : monsterCo1GeometryVectorRowNormalize [15, 155, 163] =
      monsterCo1GeometryVectorRowNormalize (monsterCo1GeometryVectorRow139) := by decide +kernel
  exact (monsterCo1GeometryVectorRowEval_eq_of_normalize _ _ _ hc).symm.trans hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
