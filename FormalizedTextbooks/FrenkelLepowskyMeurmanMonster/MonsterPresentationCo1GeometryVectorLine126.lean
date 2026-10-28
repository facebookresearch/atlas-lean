/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint040
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint127
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint150

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 126 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine126 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint40 monsterCo1GeometryVectorPoint127
      monsterCo1GeometryVectorPoint150 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint40Transport _ _ _
    591872 589824 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint40Transport⁻¹
        monsterCo1GeometryVectorPoint127.val = _
    rw [monsterCo1GeometryVectorPoint40Transport_inverse_binary,
      monsterCo1GeometryVectorPoint127_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint40Transport⁻¹
        monsterCo1GeometryVectorPoint150.val = _
    rw [monsterCo1GeometryVectorPoint40Transport_inverse_binary,
      monsterCo1GeometryVectorPoint150_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
