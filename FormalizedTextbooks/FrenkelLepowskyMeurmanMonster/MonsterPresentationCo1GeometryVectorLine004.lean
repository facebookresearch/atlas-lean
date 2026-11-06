/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint028

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 4 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine4 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint2 monsterCo1GeometryVectorPoint4
      monsterCo1GeometryVectorPoint28 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint2Transport _ _ _
    4853760 4855808 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint2Transport⁻¹
        monsterCo1GeometryVectorPoint4.val = _
    rw [monsterCo1GeometryVectorPoint2Transport_inverse_binary,
      monsterCo1GeometryVectorPoint4_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint2Transport⁻¹
        monsterCo1GeometryVectorPoint28.val = _
    rw [monsterCo1GeometryVectorPoint2Transport_inverse_binary,
      monsterCo1GeometryVectorPoint28_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
