/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint042
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint049
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint097

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 73 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine73 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint42 monsterCo1GeometryVectorPoint49
      monsterCo1GeometryVectorPoint97 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint42Transport _ _ _
    708608 710656 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint42Transport⁻¹
        monsterCo1GeometryVectorPoint49.val = _
    rw [monsterCo1GeometryVectorPoint42Transport_inverse_binary,
      monsterCo1GeometryVectorPoint49_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint42Transport⁻¹
        monsterCo1GeometryVectorPoint97.val = _
    rw [monsterCo1GeometryVectorPoint42Transport_inverse_binary,
      monsterCo1GeometryVectorPoint97_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
