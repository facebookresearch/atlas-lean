/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint162
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint169

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 145 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine145 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint12 monsterCo1GeometryVectorPoint162
      monsterCo1GeometryVectorPoint169 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint12Transport _ _ _
    1640448 1638400 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint12Transport⁻¹
        monsterCo1GeometryVectorPoint162.val = _
    rw [monsterCo1GeometryVectorPoint12Transport_inverse_binary,
      monsterCo1GeometryVectorPoint162_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint12Transport⁻¹
        monsterCo1GeometryVectorPoint169.val = _
    rw [monsterCo1GeometryVectorPoint12Transport_inverse_binary,
      monsterCo1GeometryVectorPoint169_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
