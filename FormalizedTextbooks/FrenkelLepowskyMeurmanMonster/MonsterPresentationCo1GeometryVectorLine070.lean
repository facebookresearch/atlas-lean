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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint046
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint094

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 70 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine70 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint30 monsterCo1GeometryVectorPoint46
      monsterCo1GeometryVectorPoint94 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint30Transport _ _ _
    4941824 4939776 1 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint30Transport⁻¹
        monsterCo1GeometryVectorPoint46.val = _
    rw [monsterCo1GeometryVectorPoint30Transport_inverse_binary,
      monsterCo1GeometryVectorPoint46_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint30Transport⁻¹
        monsterCo1GeometryVectorPoint94.val = _
    rw [monsterCo1GeometryVectorPoint30Transport_inverse_binary,
      monsterCo1GeometryVectorPoint94_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
