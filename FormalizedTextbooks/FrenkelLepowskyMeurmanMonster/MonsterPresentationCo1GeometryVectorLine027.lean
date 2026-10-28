/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint017
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint051

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 27 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine27 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint12 monsterCo1GeometryVectorPoint17
      monsterCo1GeometryVectorPoint51 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint12Transport _ _ _
    708608 710656 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint12Transport⁻¹
        monsterCo1GeometryVectorPoint17.val = _
    rw [monsterCo1GeometryVectorPoint12Transport_inverse_binary,
      monsterCo1GeometryVectorPoint17_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint12Transport⁻¹
        monsterCo1GeometryVectorPoint51.val = _
    rw [monsterCo1GeometryVectorPoint12Transport_inverse_binary,
      monsterCo1GeometryVectorPoint51_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
