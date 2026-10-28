/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint091
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint160
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint168

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 144 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine144 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint91 monsterCo1GeometryVectorPoint160
      monsterCo1GeometryVectorPoint168 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint91Transport _ _ _
    1837056 1835008 6 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint91Transport⁻¹
        monsterCo1GeometryVectorPoint160.val = _
    rw [monsterCo1GeometryVectorPoint91Transport_inverse_binary,
      monsterCo1GeometryVectorPoint160_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint91Transport⁻¹
        monsterCo1GeometryVectorPoint168.val = _
    rw [monsterCo1GeometryVectorPoint91Transport_inverse_binary,
      monsterCo1GeometryVectorPoint168_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
