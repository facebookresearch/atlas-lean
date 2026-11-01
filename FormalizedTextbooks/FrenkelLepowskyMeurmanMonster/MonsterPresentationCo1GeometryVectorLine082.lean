/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint056
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint058
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint106

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 82 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine82 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint56 monsterCo1GeometryVectorPoint58
      monsterCo1GeometryVectorPoint106 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint56Transport _ _ _
    528384 530432 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint56Transport⁻¹
        monsterCo1GeometryVectorPoint58.val = _
    rw [monsterCo1GeometryVectorPoint56Transport_inverse_binary,
      monsterCo1GeometryVectorPoint58_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint56Transport⁻¹
        monsterCo1GeometryVectorPoint106.val = _
    rw [monsterCo1GeometryVectorPoint56Transport_inverse_binary,
      monsterCo1GeometryVectorPoint106_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
