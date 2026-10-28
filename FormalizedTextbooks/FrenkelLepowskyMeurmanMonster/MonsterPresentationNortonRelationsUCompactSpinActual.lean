/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact actual Norton spin factor has a single sixty-four-term Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixedAssembly

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual complete Norton spin factor equals the genuine centrally corrected compact word. -/
theorem monsterNortonUCompactPositiveSpin_eq :
    monsterNortonUFiber.val.1 = monsterNortonUCompactPositiveSpin :=
  monsterNortonUCompactPositiveSpin_eq_of_fixed monsterNortonUFiber_spin_fixed

/-- Every actual Norton spin action is the negative of the explicit one-Gaussian candidate. -/
theorem monsterNortonUCompactSpin_actual_apply (x : SpinSpace) :
    monsterNortonUFiber.val.1.val x = -monsterNortonUCompactSpin.val x := by
  rw [monsterNortonUCompactPositiveSpin_eq, monsterNortonUCompactPositiveSpin_apply]

/-- The exact one-Gaussian integer numerator gives actual Norton spin action, with its true sign. -/
theorem monsterNortonUCompactSpin_actual_embed (v : NortonUIntegerVector) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed v) =
      (-1 / 8 : ℝ) • nortonUIntegerEmbed (monsterNortonUCompactNumerator v) := by
  rw [monsterNortonUCompactSpin_actual_apply, monsterNortonUCompactNumerator_embed]
  rw [← neg_smul]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
