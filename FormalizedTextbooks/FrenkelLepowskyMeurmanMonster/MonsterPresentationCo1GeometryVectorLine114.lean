/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint034
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint088
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint138

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 114 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine114 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint34 monsterCo1GeometryVectorPoint88
      monsterCo1GeometryVectorPoint138 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint34Transport _ _ _
    3342336 3344384 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint34Transport⁻¹
        monsterCo1GeometryVectorPoint88.val = _
    rw [monsterCo1GeometryVectorPoint34Transport_inverse_binary,
      monsterCo1GeometryVectorPoint88_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint34Transport⁻¹
        monsterCo1GeometryVectorPoint138.val = _
    rw [monsterCo1GeometryVectorPoint34Transport_inverse_binary,
      monsterCo1GeometryVectorPoint138_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
