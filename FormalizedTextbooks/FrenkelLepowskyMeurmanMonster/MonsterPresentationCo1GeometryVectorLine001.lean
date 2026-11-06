/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint002
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint025

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 1 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine1 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint0 monsterCo1GeometryVectorPoint2
      monsterCo1GeometryVectorPoint25 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint0Transport _ _ _
    5181440 5183488 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint0Transport⁻¹
        monsterCo1GeometryVectorPoint2.val = _
    rw [monsterCo1GeometryVectorPoint0Transport_inverse_binary,
      monsterCo1GeometryVectorPoint2_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint0Transport⁻¹
        monsterCo1GeometryVectorPoint25.val = _
    rw [monsterCo1GeometryVectorPoint0Transport_inverse_binary,
      monsterCo1GeometryVectorPoint25_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
