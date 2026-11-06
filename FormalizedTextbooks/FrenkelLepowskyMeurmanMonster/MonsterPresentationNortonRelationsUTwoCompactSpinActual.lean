/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact positive scalar binding of the rank-four Gaussian to the genuine squared Norton spin. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoCompactSpinQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoCompactSpinAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixedAssembly

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
-- Exactly sixteen full monomially corrected integer summands determine the remaining global sign.
/-- The genuine compact numerator is positive 104 at the actual fixed vector's zero coordinate. -/
theorem monsterNortonUTwoCompactNumerator_fixed_zero :
    monsterNortonUTwoCompactNumerator (monsterNortonFixedState 0) 0 = 104 := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- The actual squared Norton operator equals the genuine compact rank-four Gaussian word. -/
theorem monsterNortonUTwoCompactSpin_actual :
    monsterNortonUFiber.val.1 ^ 2 = monsterNortonUTwoCompactSpin := by
  let v : SpinSpace := nortonUIntegerEmbed (monsterNortonFixedState 0)
  have hv : (monsterNortonUFiber.val.1 ^ 2).val v = v := by
    rw [pow_two, nortonUIntegerSpin_mul_apply]
    rw [monsterNortonUFiber_spin_fixed, monsterNortonUFiber_spin_fixed]
  have hz : nortonUIntegerLabel (0 : SpinIndex) = 0 := by decide +kernel
  have ht : monsterNortonUTwoCompactSpin.val v 0 = v 0 := by
    have h := congrFun (monsterNortonUTwoCompactNumerator_embed (monsterNortonFixedState 0)) 0
    simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed, hz,
      monsterNortonUTwoCompactNumerator_fixed_zero] at h
    change monsterNortonUTwoCompactSpin.val v 0 = _ at h
    rw [h]
    dsimp only [v, nortonUIntegerEmbed]
    rw [hz, monsterNortonFixedState_zero_zero]
    norm_num
  have hn : v 0 ≠ 0 := by
    dsimp only [v, nortonUIntegerEmbed]
    rw [hz, monsterNortonFixedState_zero_zero]
    norm_num
  exact monsterNortonUTwoCompactSpin_eq_of_fixed_coordinate v 0 hv ht hn

/-- The actual full squared spin action has the sixteen-term numerator and normalization one
  fourth. -/
theorem monsterNortonUTwoCompactSpin_actual_embed (v : NortonUIntegerVector) :
    (monsterNortonUFiber.val.1 ^ 2).val (nortonUIntegerEmbed v) =
      (1 / 4 : ℝ) • nortonUIntegerEmbed (monsterNortonUTwoCompactNumerator v) := by
  rw [monsterNortonUTwoCompactSpin_actual]
  exact monsterNortonUTwoCompactNumerator_embed v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
