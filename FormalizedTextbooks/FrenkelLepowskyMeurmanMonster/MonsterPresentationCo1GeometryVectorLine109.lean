/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint019
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint085
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint133

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 109 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine109 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint19 monsterCo1GeometryVectorPoint85
      monsterCo1GeometryVectorPoint133 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint19Transport _ _ _
    655360 657408 5 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint19Transport⁻¹
        monsterCo1GeometryVectorPoint85.val = _
    rw [monsterCo1GeometryVectorPoint19Transport_inverse_binary,
      monsterCo1GeometryVectorPoint85_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint19Transport⁻¹
        monsterCo1GeometryVectorPoint133.val = _
    rw [monsterCo1GeometryVectorPoint19Transport_inverse_binary,
      monsterCo1GeometryVectorPoint133_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
