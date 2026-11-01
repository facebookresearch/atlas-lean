/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint030
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint048
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint096

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 72 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine72 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint30 monsterCo1GeometryVectorPoint48
      monsterCo1GeometryVectorPoint96 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint30Transport _ _ _
    8028160 8030208 3 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint30Transport⁻¹
        monsterCo1GeometryVectorPoint48.val = _
    rw [monsterCo1GeometryVectorPoint30Transport_inverse_binary,
      monsterCo1GeometryVectorPoint48_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint30Transport⁻¹
        monsterCo1GeometryVectorPoint96.val = _
    rw [monsterCo1GeometryVectorPoint30Transport_inverse_binary,
      monsterCo1GeometryVectorPoint96_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
