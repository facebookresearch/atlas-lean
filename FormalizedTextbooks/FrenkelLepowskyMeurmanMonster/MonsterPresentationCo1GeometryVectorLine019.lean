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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint043

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 19 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine19 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint1 monsterCo1GeometryVectorPoint13
      monsterCo1GeometryVectorPoint43 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint1Transport _ _ _
    6864896 6866944 2 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint1Transport⁻¹
        monsterCo1GeometryVectorPoint13.val = _
    rw [monsterCo1GeometryVectorPoint1Transport_inverse_binary,
      monsterCo1GeometryVectorPoint13_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint1Transport⁻¹
        monsterCo1GeometryVectorPoint43.val = _
    rw [monsterCo1GeometryVectorPoint1Transport_inverse_binary,
      monsterCo1GeometryVectorPoint43_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
