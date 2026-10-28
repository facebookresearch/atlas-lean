/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint036
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint065
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint112

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 88 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine88 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint36 monsterCo1GeometryVectorPoint65
      monsterCo1GeometryVectorPoint112 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint36Transport _ _ _
    4571136 4573184 2 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint36Transport⁻¹
        monsterCo1GeometryVectorPoint65.val = _
    rw [monsterCo1GeometryVectorPoint36Transport_inverse_binary,
      monsterCo1GeometryVectorPoint65_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint36Transport⁻¹
        monsterCo1GeometryVectorPoint112.val = _
    rw [monsterCo1GeometryVectorPoint36Transport_inverse_binary,
      monsterCo1GeometryVectorPoint112_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
