/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint018
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint122

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 98 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine98 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint18 monsterCo1GeometryVectorPoint75
      monsterCo1GeometryVectorPoint122 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint18Transport _ _ _
    655360 657408 5 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint18Transport⁻¹
        monsterCo1GeometryVectorPoint75.val = _
    rw [monsterCo1GeometryVectorPoint18Transport_inverse_binary,
      monsterCo1GeometryVectorPoint75_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint18Transport⁻¹
        monsterCo1GeometryVectorPoint122.val = _
    rw [monsterCo1GeometryVectorPoint18Transport_inverse_binary,
      monsterCo1GeometryVectorPoint122_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
