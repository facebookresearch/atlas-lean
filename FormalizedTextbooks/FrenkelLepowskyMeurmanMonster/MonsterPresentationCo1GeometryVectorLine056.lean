/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint014
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint036
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint080

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 56 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine56 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint14 monsterCo1GeometryVectorPoint36
      monsterCo1GeometryVectorPoint80 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint14Transport _ _ _
    8128512 8126464 6 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint14Transport⁻¹
        monsterCo1GeometryVectorPoint36.val = _
    rw [monsterCo1GeometryVectorPoint14Transport_inverse_binary,
      monsterCo1GeometryVectorPoint36_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint14Transport⁻¹
        monsterCo1GeometryVectorPoint80.val = _
    rw [monsterCo1GeometryVectorPoint14Transport_inverse_binary,
      monsterCo1GeometryVectorPoint80_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
