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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint136
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint152

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 128 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine128 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint22 monsterCo1GeometryVectorPoint136
      monsterCo1GeometryVectorPoint152 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint22Transport _ _ _
    851968 854016 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint22Transport⁻¹
        monsterCo1GeometryVectorPoint136.val = _
    rw [monsterCo1GeometryVectorPoint22Transport_inverse_binary,
      monsterCo1GeometryVectorPoint136_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint22Transport⁻¹
        monsterCo1GeometryVectorPoint152.val = _
    rw [monsterCo1GeometryVectorPoint22Transport_inverse_binary,
      monsterCo1GeometryVectorPoint152_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
