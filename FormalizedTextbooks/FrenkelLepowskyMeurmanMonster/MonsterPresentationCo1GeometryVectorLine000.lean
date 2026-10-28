/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint000
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint001
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint024

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 0 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine0 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint0 monsterCo1GeometryVectorPoint1
      monsterCo1GeometryVectorPoint24 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint0Transport _ _ _
    4194304 4196352 10 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint0Transport⁻¹
        monsterCo1GeometryVectorPoint1.val = _
    rw [monsterCo1GeometryVectorPoint0Transport_inverse_binary,
      monsterCo1GeometryVectorPoint1_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint0Transport⁻¹
        monsterCo1GeometryVectorPoint24.val = _
    rw [monsterCo1GeometryVectorPoint0Transport_inverse_binary,
      monsterCo1GeometryVectorPoint24_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
