/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint032
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint040
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint089

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 65 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine65 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint32 monsterCo1GeometryVectorPoint40
      monsterCo1GeometryVectorPoint89 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint32Transport _ _ _
    4200448 4198400 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint32Transport⁻¹
        monsterCo1GeometryVectorPoint40.val = _
    rw [monsterCo1GeometryVectorPoint32Transport_inverse_binary,
      monsterCo1GeometryVectorPoint40_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint32Transport⁻¹
        monsterCo1GeometryVectorPoint89.val = _
    rw [monsterCo1GeometryVectorPoint32Transport_inverse_binary,
      monsterCo1GeometryVectorPoint89_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
