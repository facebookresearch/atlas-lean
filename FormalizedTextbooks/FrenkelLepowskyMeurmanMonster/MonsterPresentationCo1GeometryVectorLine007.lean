/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint004
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint031

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 7 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine7 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint4 monsterCo1GeometryVectorPoint5
      monsterCo1GeometryVectorPoint31 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint4Transport _ _ _
    5179392 5177344 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint4Transport⁻¹
        monsterCo1GeometryVectorPoint5.val = _
    rw [monsterCo1GeometryVectorPoint4Transport_inverse_binary,
      monsterCo1GeometryVectorPoint5_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint4Transport⁻¹
        monsterCo1GeometryVectorPoint31.val = _
    rw [monsterCo1GeometryVectorPoint4Transport_inverse_binary,
      monsterCo1GeometryVectorPoint31_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
