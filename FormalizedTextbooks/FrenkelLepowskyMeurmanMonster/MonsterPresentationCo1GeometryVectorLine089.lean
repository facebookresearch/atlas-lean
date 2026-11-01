/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint065
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint113

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 89 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine89 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint57 monsterCo1GeometryVectorPoint65
      monsterCo1GeometryVectorPoint113 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint57Transport _ _ _
    317440 315392 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint57Transport⁻¹
        monsterCo1GeometryVectorPoint65.val = _
    rw [monsterCo1GeometryVectorPoint57Transport_inverse_binary,
      monsterCo1GeometryVectorPoint65_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint57Transport⁻¹
        monsterCo1GeometryVectorPoint113.val = _
    rw [monsterCo1GeometryVectorPoint57Transport_inverse_binary,
      monsterCo1GeometryVectorPoint113_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
