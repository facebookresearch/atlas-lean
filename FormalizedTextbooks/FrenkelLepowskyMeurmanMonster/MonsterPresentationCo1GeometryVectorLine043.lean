/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint067

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 43 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine43 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint17 monsterCo1GeometryVectorPoint30
      monsterCo1GeometryVectorPoint67 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint17Transport _ _ _
    655360 657408 5 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint17Transport⁻¹
        monsterCo1GeometryVectorPoint30.val = _
    rw [monsterCo1GeometryVectorPoint17Transport_inverse_binary,
      monsterCo1GeometryVectorPoint30_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint17Transport⁻¹
        monsterCo1GeometryVectorPoint67.val = _
    rw [monsterCo1GeometryVectorPoint17Transport_inverse_binary,
      monsterCo1GeometryVectorPoint67_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
