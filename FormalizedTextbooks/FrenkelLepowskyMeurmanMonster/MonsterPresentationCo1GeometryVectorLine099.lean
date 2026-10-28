/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint052
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint075
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint123

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 99 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine99 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint52 monsterCo1GeometryVectorPoint75
      monsterCo1GeometryVectorPoint123 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint52Transport _ _ _
    655360 657408 5 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint52Transport⁻¹
        monsterCo1GeometryVectorPoint75.val = _
    rw [monsterCo1GeometryVectorPoint52Transport_inverse_binary,
      monsterCo1GeometryVectorPoint75_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint52Transport⁻¹
        monsterCo1GeometryVectorPoint123.val = _
    rw [monsterCo1GeometryVectorPoint52Transport_inverse_binary,
      monsterCo1GeometryVectorPoint123_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
