/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint003
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint044

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 20 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine20 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint3 monsterCo1GeometryVectorPoint13
      monsterCo1GeometryVectorPoint44 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint3Transport _ _ _
    6864896 6866944 2 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint3Transport⁻¹
        monsterCo1GeometryVectorPoint13.val = _
    rw [monsterCo1GeometryVectorPoint3Transport_inverse_binary,
      monsterCo1GeometryVectorPoint13_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint3Transport⁻¹
        monsterCo1GeometryVectorPoint44.val = _
    rw [monsterCo1GeometryVectorPoint3Transport_inverse_binary,
      monsterCo1GeometryVectorPoint44_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
