/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint026
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint043
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint092

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 68 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine68 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint26 monsterCo1GeometryVectorPoint43
      monsterCo1GeometryVectorPoint92 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint26Transport _ _ _
    6864896 6866944 2 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint26Transport⁻¹
        monsterCo1GeometryVectorPoint43.val = _
    rw [monsterCo1GeometryVectorPoint26Transport_inverse_binary,
      monsterCo1GeometryVectorPoint43_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint26Transport⁻¹
        monsterCo1GeometryVectorPoint92.val = _
    rw [monsterCo1GeometryVectorPoint26Transport_inverse_binary,
      monsterCo1GeometryVectorPoint92_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
