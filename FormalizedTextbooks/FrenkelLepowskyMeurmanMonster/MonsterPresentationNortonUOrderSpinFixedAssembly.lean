/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A nonzero integer fixed vector for the actual literal Norton spin word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinFixed8

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual complete integer word sends the candidate to exactly 128 times itself. -/
theorem monsterNortonUIntegerU_fixed :
    nortonUIntegerU (monsterNortonFixedState 0) = (128 : ℤ) • monsterNortonFixedState 0 := by
  rw [← monsterNortonSpinFastU_eq]
  unfold monsterNortonSpinFastU
  rw [monsterNortonFixedPrimitive0, monsterNortonFixedPrimitive1, monsterNortonFixedPrimitive2,
    monsterNortonFixedPrimitive3, monsterNortonFixedPrimitive4, monsterNortonFixedPrimitive5,
    monsterNortonFixedPrimitive6, monsterNortonFixedPrimitive7, monsterNortonFixedPrimitive8,
    monsterNortonFixedState_final]

private theorem embed_smul (c : ℤ) (v : NortonUIntegerVector) :
    nortonUIntegerEmbed (c • v) = (c : ℝ) • nortonUIntegerEmbed v := by
  funext t
  simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, Int.cast_mul]

/-- The embedded candidate remains nonzero, with exact real zero-label coordinate 26. -/
theorem monsterNortonFixedEmbed_zero :
    nortonUIntegerEmbed (monsterNortonFixedState 0) (0 : SpinIndex) = 26 := by
  have h : nortonUIntegerLabel (0 : SpinIndex) = 0 := by
    apply Fin.ext
    simp [nortonUIntegerLabel]
  change (monsterNortonFixedState 0 (nortonUIntegerLabel 0) : ℝ) = 26
  rw [h, monsterNortonFixedState_zero_zero]
  norm_num

/-- The actual literal spin word fixes the concrete nonzero embedded integer vector. -/
theorem monsterNortonUFiber_spin_fixed :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed (monsterNortonFixedState 0)) =
      nortonUIntegerEmbed (monsterNortonFixedState 0) := by
  rw [nortonUIntegerU_embed, monsterNortonUIntegerU_fixed, embed_smul, smul_smul]
  have h : (1 / 128 : ℝ) * (128 : ℤ) = 1 := by norm_num
  rw [h, one_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
