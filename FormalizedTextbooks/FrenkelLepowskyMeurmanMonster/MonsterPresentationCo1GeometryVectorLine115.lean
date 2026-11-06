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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint088
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint139

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 115 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine115 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint53 monsterCo1GeometryVectorPoint88
      monsterCo1GeometryVectorPoint139 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint53Transport _ _ _
    3082240 3080192 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint53Transport⁻¹
        monsterCo1GeometryVectorPoint88.val = _
    rw [monsterCo1GeometryVectorPoint53Transport_inverse_binary,
      monsterCo1GeometryVectorPoint88_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint53Transport⁻¹
        monsterCo1GeometryVectorPoint139.val = _
    rw [monsterCo1GeometryVectorPoint53Transport_inverse_binary,
      monsterCo1GeometryVectorPoint139_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
