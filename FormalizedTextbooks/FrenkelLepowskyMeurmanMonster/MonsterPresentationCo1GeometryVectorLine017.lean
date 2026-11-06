/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint006
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint041

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 17 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine17 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint6 monsterCo1GeometryVectorPoint11
      monsterCo1GeometryVectorPoint41 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint6Transport _ _ _
    4853760 4855808 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint6Transport⁻¹
        monsterCo1GeometryVectorPoint11.val = _
    rw [monsterCo1GeometryVectorPoint6Transport_inverse_binary,
      monsterCo1GeometryVectorPoint11_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint6Transport⁻¹
        monsterCo1GeometryVectorPoint41.val = _
    rw [monsterCo1GeometryVectorPoint6Transport_inverse_binary,
      monsterCo1GeometryVectorPoint41_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
