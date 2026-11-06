/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint076

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 52 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine52 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint30 monsterCo1GeometryVectorPoint35
      monsterCo1GeometryVectorPoint76 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint30Transport _ _ _
    4198400 4200448 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint30Transport⁻¹
        monsterCo1GeometryVectorPoint35.val = _
    rw [monsterCo1GeometryVectorPoint30Transport_inverse_binary,
      monsterCo1GeometryVectorPoint35_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint30Transport⁻¹
        monsterCo1GeometryVectorPoint76.val = _
    rw [monsterCo1GeometryVectorPoint30Transport_inverse_binary,
      monsterCo1GeometryVectorPoint76_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
