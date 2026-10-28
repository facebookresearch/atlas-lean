/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint081
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint095
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint141

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 117 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine117 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint81 monsterCo1GeometryVectorPoint95
      monsterCo1GeometryVectorPoint141 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint81Transport _ _ _
    3753984 3751936 2 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint81Transport⁻¹
        monsterCo1GeometryVectorPoint95.val = _
    rw [monsterCo1GeometryVectorPoint81Transport_inverse_binary,
      monsterCo1GeometryVectorPoint95_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint81Transport⁻¹
        monsterCo1GeometryVectorPoint141.val = _
    rw [monsterCo1GeometryVectorPoint81Transport_inverse_binary,
      monsterCo1GeometryVectorPoint141_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
