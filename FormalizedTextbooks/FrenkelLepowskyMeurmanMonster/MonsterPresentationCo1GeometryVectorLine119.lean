/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint022
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint100
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint143

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 119 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine119 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint22 monsterCo1GeometryVectorPoint100
      monsterCo1GeometryVectorPoint143 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint22Transport _ _ _
    655360 657408 5 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint22Transport⁻¹
        monsterCo1GeometryVectorPoint100.val = _
    rw [monsterCo1GeometryVectorPoint22Transport_inverse_binary,
      monsterCo1GeometryVectorPoint100_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint22Transport⁻¹
        monsterCo1GeometryVectorPoint143.val = _
    rw [monsterCo1GeometryVectorPoint22Transport_inverse_binary,
      monsterCo1GeometryVectorPoint143_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
