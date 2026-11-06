/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact Norton U fixed vector also fixes the pure Singer permutation lift. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerSpinFixedData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixedAssembly

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse spin lift fixes the real embedded nonzero Norton vector. -/
theorem monsterNortonSingerSpin_inverse_fixed :
    monsterNortonSingerSpin⁻¹.val (nortonUIntegerEmbed (monsterNortonFixedState 0)) =
      nortonUIntegerEmbed (monsterNortonFixedState 0) := by
  ext t
  change (monsterNortonFixedState 0 (nortonUIntegerLabel (monsterNortonSingerCode 0 t)) : ℝ) =
    (monsterNortonFixedState 0 (nortonUIntegerLabel t) : ℝ)
  obtain ⟨n, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [nortonUIntegerLabel_coeff, monsterNortonSinger_fixed_state_certificate]

private theorem fixed_of_inverse_fixed (s : SpinHolomorph) (v : SpinSpace)
    (h : s⁻¹.val v = v) : s.val v = v := by
  have he := congrArg s.val h
  change s.val (s.val.symm v) = s.val v at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

/-- The forward actual spin lift fixes the same nonzero vector. -/
theorem monsterNortonSingerSpin_fixed :
    monsterNortonSingerSpin.val (nortonUIntegerEmbed (monsterNortonFixedState 0)) =
      nortonUIntegerEmbed (monsterNortonFixedState 0) :=
  fixed_of_inverse_fixed _ _ monsterNortonSingerSpin_inverse_fixed

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
