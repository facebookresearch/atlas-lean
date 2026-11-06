/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint007
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint013
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint045

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 21 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine21 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint7 monsterCo1GeometryVectorPoint13
      monsterCo1GeometryVectorPoint45 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint7Transport _ _ _
    2623488 2621440 7 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint7Transport⁻¹
        monsterCo1GeometryVectorPoint13.val = _
    rw [monsterCo1GeometryVectorPoint7Transport_inverse_binary,
      monsterCo1GeometryVectorPoint13_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint7Transport⁻¹
        monsterCo1GeometryVectorPoint45.val = _
    rw [monsterCo1GeometryVectorPoint7Transport_inverse_binary,
      monsterCo1GeometryVectorPoint45_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
