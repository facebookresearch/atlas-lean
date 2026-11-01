/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint005
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint153
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint154

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 130 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine130 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint5 monsterCo1GeometryVectorPoint153
      monsterCo1GeometryVectorPoint154 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint5Transport _ _ _
    2293760 2295808 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint5Transport⁻¹
        monsterCo1GeometryVectorPoint153.val = _
    rw [monsterCo1GeometryVectorPoint5Transport_inverse_binary,
      monsterCo1GeometryVectorPoint153_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint5Transport⁻¹
        monsterCo1GeometryVectorPoint154.val = _
    rw [monsterCo1GeometryVectorPoint5Transport_inverse_binary,
      monsterCo1GeometryVectorPoint154_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
