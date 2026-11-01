/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 6 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine6 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint1 monsterCo1GeometryVectorPoint5
      monsterCo1GeometryVectorPoint30 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint1Transport _ _ _
    395264 393216 5 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint1Transport⁻¹
        monsterCo1GeometryVectorPoint5.val = _
    rw [monsterCo1GeometryVectorPoint1Transport_inverse_binary,
      monsterCo1GeometryVectorPoint5_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint1Transport⁻¹
        monsterCo1GeometryVectorPoint30.val = _
    rw [monsterCo1GeometryVectorPoint1Transport_inverse_binary,
      monsterCo1GeometryVectorPoint30_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
