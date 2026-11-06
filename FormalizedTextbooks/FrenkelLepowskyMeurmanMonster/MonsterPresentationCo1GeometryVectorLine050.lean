/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint010
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint035
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint074

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 50 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine50 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint10 monsterCo1GeometryVectorPoint35
      monsterCo1GeometryVectorPoint74 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint10Transport _ _ _
    4915200 4917248 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint10Transport⁻¹
        monsterCo1GeometryVectorPoint35.val = _
    rw [monsterCo1GeometryVectorPoint10Transport_inverse_binary,
      monsterCo1GeometryVectorPoint35_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint10Transport⁻¹
        monsterCo1GeometryVectorPoint74.val = _
    rw [monsterCo1GeometryVectorPoint10Transport_inverse_binary,
      monsterCo1GeometryVectorPoint74_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
