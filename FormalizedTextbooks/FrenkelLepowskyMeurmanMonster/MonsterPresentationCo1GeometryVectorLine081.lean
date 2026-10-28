/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint055
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint057
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint105

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 81 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine81 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint55 monsterCo1GeometryVectorPoint57
      monsterCo1GeometryVectorPoint105 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint55Transport _ _ _
    4784128 4786176 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint55Transport⁻¹
        monsterCo1GeometryVectorPoint57.val = _
    rw [monsterCo1GeometryVectorPoint55Transport_inverse_binary,
      monsterCo1GeometryVectorPoint57_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint55Transport⁻¹
        monsterCo1GeometryVectorPoint105.val = _
    rw [monsterCo1GeometryVectorPoint55Transport_inverse_binary,
      monsterCo1GeometryVectorPoint105_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
