/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint140
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint154
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint161

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 137 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine137 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint140 monsterCo1GeometryVectorPoint154
      monsterCo1GeometryVectorPoint161 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint140Transport _ _ _
    135168 137216 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint140Transport⁻¹
        monsterCo1GeometryVectorPoint154.val = _
    rw [monsterCo1GeometryVectorPoint140Transport_inverse_binary,
      monsterCo1GeometryVectorPoint154_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint140Transport⁻¹
        monsterCo1GeometryVectorPoint161.val = _
    rw [monsterCo1GeometryVectorPoint140Transport_inverse_binary,
      monsterCo1GeometryVectorPoint161_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
