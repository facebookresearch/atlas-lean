/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint022
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint054

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 30 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine30 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint7 monsterCo1GeometryVectorPoint22
      monsterCo1GeometryVectorPoint54 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint7Transport _ _ _
    7073792 7075840 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint7Transport⁻¹
        monsterCo1GeometryVectorPoint22.val = _
    rw [monsterCo1GeometryVectorPoint7Transport_inverse_binary,
      monsterCo1GeometryVectorPoint22_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint7Transport⁻¹
        monsterCo1GeometryVectorPoint54.val = _
    rw [monsterCo1GeometryVectorPoint7Transport_inverse_binary,
      monsterCo1GeometryVectorPoint54_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
