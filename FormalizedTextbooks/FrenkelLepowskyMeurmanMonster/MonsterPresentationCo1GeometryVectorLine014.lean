/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint038

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 14 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine14 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint5 monsterCo1GeometryVectorPoint9
      monsterCo1GeometryVectorPoint38 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint5Transport _ _ _
    5183488 5181440 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint5Transport⁻¹
        monsterCo1GeometryVectorPoint9.val = _
    rw [monsterCo1GeometryVectorPoint5Transport_inverse_binary,
      monsterCo1GeometryVectorPoint9_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint5Transport⁻¹
        monsterCo1GeometryVectorPoint38.val = _
    rw [monsterCo1GeometryVectorPoint5Transport_inverse_binary,
      monsterCo1GeometryVectorPoint38_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
