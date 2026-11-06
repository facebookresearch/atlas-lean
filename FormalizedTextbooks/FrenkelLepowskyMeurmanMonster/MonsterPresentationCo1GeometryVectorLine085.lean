/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint009
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint061
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint109

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 85 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine85 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint9 monsterCo1GeometryVectorPoint61
      monsterCo1GeometryVectorPoint109 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint9Transport _ _ _
    5046272 5048320 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint9Transport⁻¹
        monsterCo1GeometryVectorPoint61.val = _
    rw [monsterCo1GeometryVectorPoint9Transport_inverse_binary,
      monsterCo1GeometryVectorPoint61_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint9Transport⁻¹
        monsterCo1GeometryVectorPoint109.val = _
    rw [monsterCo1GeometryVectorPoint9Transport_inverse_binary,
      monsterCo1GeometryVectorPoint109_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
