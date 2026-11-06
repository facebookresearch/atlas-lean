/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint073
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint097
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint142

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 118 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine118 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint73 monsterCo1GeometryVectorPoint97
      monsterCo1GeometryVectorPoint142 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint73Transport _ _ _
    7763968 7761920 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint73Transport⁻¹
        monsterCo1GeometryVectorPoint97.val = _
    rw [monsterCo1GeometryVectorPoint73Transport_inverse_binary,
      monsterCo1GeometryVectorPoint97_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint73Transport⁻¹
        monsterCo1GeometryVectorPoint142.val = _
    rw [monsterCo1GeometryVectorPoint73Transport_inverse_binary,
      monsterCo1GeometryVectorPoint142_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
