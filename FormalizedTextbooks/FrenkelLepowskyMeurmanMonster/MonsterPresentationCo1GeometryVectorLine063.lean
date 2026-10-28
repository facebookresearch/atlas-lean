/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint029
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint039
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint087

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 63 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine63 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint29 monsterCo1GeometryVectorPoint39
      monsterCo1GeometryVectorPoint87 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint29Transport _ _ _
    5052416 5050368 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint29Transport⁻¹
        monsterCo1GeometryVectorPoint39.val = _
    rw [monsterCo1GeometryVectorPoint29Transport_inverse_binary,
      monsterCo1GeometryVectorPoint39_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint29Transport⁻¹
        monsterCo1GeometryVectorPoint87.val = _
    rw [monsterCo1GeometryVectorPoint29Transport_inverse_binary,
      monsterCo1GeometryVectorPoint87_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
