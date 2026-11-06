/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint081
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint126

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 102 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine102 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint13 monsterCo1GeometryVectorPoint81
      monsterCo1GeometryVectorPoint126 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint13Transport _ _ _
    983040 985088 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint13Transport⁻¹
        monsterCo1GeometryVectorPoint81.val = _
    rw [monsterCo1GeometryVectorPoint13Transport_inverse_binary,
      monsterCo1GeometryVectorPoint81_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint13Transport⁻¹
        monsterCo1GeometryVectorPoint126.val = _
    rw [monsterCo1GeometryVectorPoint13Transport_inverse_binary,
      monsterCo1GeometryVectorPoint126_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
