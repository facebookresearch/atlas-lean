/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint155
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint163

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 139 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine139 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint15 monsterCo1GeometryVectorPoint155
      monsterCo1GeometryVectorPoint163 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint15Transport _ _ _
    528384 530432 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint15Transport⁻¹
        monsterCo1GeometryVectorPoint155.val = _
    rw [monsterCo1GeometryVectorPoint15Transport_inverse_binary,
      monsterCo1GeometryVectorPoint155_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint15Transport⁻¹
        monsterCo1GeometryVectorPoint163.val = _
    rw [monsterCo1GeometryVectorPoint15Transport_inverse_binary,
      monsterCo1GeometryVectorPoint163_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
