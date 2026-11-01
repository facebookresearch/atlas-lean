/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint146
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint156
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint166

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 142 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine142 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint146 monsterCo1GeometryVectorPoint156
      monsterCo1GeometryVectorPoint166 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint146Transport _ _ _
    3371008 3373056 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint146Transport⁻¹
        monsterCo1GeometryVectorPoint156.val = _
    rw [monsterCo1GeometryVectorPoint146Transport_inverse_binary,
      monsterCo1GeometryVectorPoint156_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint146Transport⁻¹
        monsterCo1GeometryVectorPoint166.val = _
    rw [monsterCo1GeometryVectorPoint146Transport_inverse_binary,
      monsterCo1GeometryVectorPoint166_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
