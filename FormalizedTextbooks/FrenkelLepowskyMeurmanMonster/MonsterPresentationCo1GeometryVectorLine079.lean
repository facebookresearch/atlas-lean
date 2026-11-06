/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint040
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint103

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 79 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine79 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint40 monsterCo1GeometryVectorPoint57
      monsterCo1GeometryVectorPoint103 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint40Transport _ _ _
    655360 657408 5 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint40Transport⁻¹
        monsterCo1GeometryVectorPoint57.val = _
    rw [monsterCo1GeometryVectorPoint40Transport_inverse_binary,
      monsterCo1GeometryVectorPoint57_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint40Transport⁻¹
        monsterCo1GeometryVectorPoint103.val = _
    rw [monsterCo1GeometryVectorPoint40Transport_inverse_binary,
      monsterCo1GeometryVectorPoint103_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
