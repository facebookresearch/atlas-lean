/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint015
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint047

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 23 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine23 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint3 monsterCo1GeometryVectorPoint15
      monsterCo1GeometryVectorPoint47 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint3Transport _ _ _
    5050368 5052416 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint3Transport⁻¹
        monsterCo1GeometryVectorPoint15.val = _
    rw [monsterCo1GeometryVectorPoint3Transport_inverse_binary,
      monsterCo1GeometryVectorPoint15_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint3Transport⁻¹
        monsterCo1GeometryVectorPoint47.val = _
    rw [monsterCo1GeometryVectorPoint3Transport_inverse_binary,
      monsterCo1GeometryVectorPoint47_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
