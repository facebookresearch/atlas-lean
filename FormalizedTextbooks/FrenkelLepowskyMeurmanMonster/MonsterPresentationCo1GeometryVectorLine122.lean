/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint090
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint101
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint146

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 122 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine122 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint90 monsterCo1GeometryVectorPoint101
      monsterCo1GeometryVectorPoint146 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint90Transport _ _ _
    4784128 4786176 4 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint90Transport⁻¹
        monsterCo1GeometryVectorPoint101.val = _
    rw [monsterCo1GeometryVectorPoint90Transport_inverse_binary,
      monsterCo1GeometryVectorPoint101_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint90Transport⁻¹
        monsterCo1GeometryVectorPoint146.val = _
    rw [monsterCo1GeometryVectorPoint90Transport_inverse_binary,
      monsterCo1GeometryVectorPoint146_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
