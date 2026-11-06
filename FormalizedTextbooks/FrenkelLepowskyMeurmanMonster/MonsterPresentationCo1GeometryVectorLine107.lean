/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint053
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint083
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint131

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 107 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine107 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint53 monsterCo1GeometryVectorPoint83
      monsterCo1GeometryVectorPoint131 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint53Transport _ _ _
    4851712 4849664 5 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint53Transport⁻¹
        monsterCo1GeometryVectorPoint83.val = _
    rw [monsterCo1GeometryVectorPoint53Transport_inverse_binary,
      monsterCo1GeometryVectorPoint83_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint53Transport⁻¹
        monsterCo1GeometryVectorPoint131.val = _
    rw [monsterCo1GeometryVectorPoint53Transport_inverse_binary,
      monsterCo1GeometryVectorPoint131_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
