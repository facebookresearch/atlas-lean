/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- One exact integer coordinate determines the central sign of the compact spin operator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixedData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Evaluate exactly sixty-four integer summands at one coordinate of the explicit vector.
/-- The uncorrected compact operator has numerator minus 208 at the distinguished coordinate. -/
theorem monsterNortonUCompactNumerator_fixed_zero :
    monsterNortonUCompactNumerator (monsterNortonFixedState 0) 0 = -208 := by
  decide +kernel

/-- Its actual real spin action therefore has coordinate minus 26. -/
theorem monsterNortonUCompactSpin_fixed_zero :
    monsterNortonUCompactSpin.val (nortonUIntegerEmbed (monsterNortonFixedState 0)) 0 = -26 := by
  have h := congrFun (monsterNortonUCompactNumerator_embed (monsterNortonFixedState 0)) 0
  have hz : nortonUIntegerLabel (0 : SpinIndex) = 0 := by decide +kernel
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed, hz,
    monsterNortonUCompactNumerator_fixed_zero] at h
  norm_num at h
  exact h

/-- The corrected genuine compact operator differs by the actual central Q involution. -/
noncomputable def monsterNortonUCompactPositiveSpin : SpinHolomorph :=
  spinHolomorphIncl (qCentral 1) * monsterNortonUCompactSpin

/-- The correction negates the full genuine real spin operator. -/
theorem monsterNortonUCompactPositiveSpin_apply (x : SpinSpace) :
    monsterNortonUCompactPositiveSpin.val x = -monsterNortonUCompactSpin.val x := by
  change spinRepresentation (qCentral 1) (monsterNortonUCompactSpin.val x) = _
  rw [spinRepresentation_central]
  simp only [qSign_one, neg_one_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
