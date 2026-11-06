/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint068
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint073
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint120

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 96 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine96 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint68 monsterCo1GeometryVectorPoint73
      monsterCo1GeometryVectorPoint120 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint68Transport _ _ _
    4524032 4521984 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint68Transport⁻¹
        monsterCo1GeometryVectorPoint73.val = _
    rw [monsterCo1GeometryVectorPoint68Transport_inverse_binary,
      monsterCo1GeometryVectorPoint73_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint68Transport⁻¹
        monsterCo1GeometryVectorPoint120.val = _
    rw [monsterCo1GeometryVectorPoint68Transport_inverse_binary,
      monsterCo1GeometryVectorPoint120_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
