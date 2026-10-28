/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- This source line is certified by the complete actual point-stabilizer two-core orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLineMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint011
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint069
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorPoint115

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 24000000 in
-- Check every original two-core generator on the complete actual transported point pair.
/-- Equation 91 is an original genuine source line with a complete two-core orbit certificate. -/
theorem monsterCo1GeometryVectorLine91 :
    monsterCo1GeometryLine monsterCo1GeometryVectorPoint11 monsterCo1GeometryVectorPoint69
      monsterCo1GeometryVectorPoint115 := by
  apply monsterCo1GeometryVectorLineMask_certificate monsterCo1GeometryVectorPoint11Transport _ _ _
    202752 200704 0 rfl
  · change co1BinaryAction monsterCo1GeometryVectorPoint11Transport⁻¹
        monsterCo1GeometryVectorPoint69.val = _
    rw [monsterCo1GeometryVectorPoint11Transport_inverse_binary,
      monsterCo1GeometryVectorPoint69_binary]
    decide +kernel
  · change co1BinaryAction monsterCo1GeometryVectorPoint11Transport⁻¹
        monsterCo1GeometryVectorPoint115.val = _
    rw [monsterCo1GeometryVectorPoint11Transport_inverse_binary,
      monsterCo1GeometryVectorPoint115_binary]
    decide +kernel
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
