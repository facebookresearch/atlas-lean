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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint012
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint042

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 18 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine18 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint0 monsterCo1GeometryVectorPoint12
      monsterCo1GeometryVectorPoint42 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint0Transport _ _ _
    4612096 4614144 1 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint0Transport⁻¹
        monsterCo1GeometryVectorPoint12.val = _
    rw [monsterCo1GeometryVectorPoint0Transport_inverse_binary,
      monsterCo1GeometryVectorPoint12_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint0Transport⁻¹
        monsterCo1GeometryVectorPoint42.val = _
    rw [monsterCo1GeometryVectorPoint0Transport_inverse_binary,
      monsterCo1GeometryVectorPoint42_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
