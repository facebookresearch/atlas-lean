/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnCircuitInitial

/-! The first four literal spin factors have their genuine signed column state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem four_spin_states (p₀ p₁ x : SpinHolomorph) (v₀ v₁ v₂ v₃ v₄ : SpinSpace)
    (h₁ : p₁.val v₀ = v₁) (h₂ : x.val v₁ = (1 / 2 : ℝ) • v₂)
    (h₃ : p₀.val v₂ = v₃) (h₄ : p₁.val v₃ = v₄) :
    (p₁ * p₀ * x * p₁).val v₀ = (1 / 2 : ℝ) • v₄ := by
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, h₁, h₂, h₃, h₄, map_smul]

private theorem embed_four (v : NortonUIntegerVector) :
    nortonUIntegerEmbed (fun n => 4 * v n) = (4 : ℝ) • nortonUIntegerEmbed v := by
  ext t
  simp only [nortonUIntegerEmbed, Int.cast_mul, Int.cast_ofNat, Pi.smul_apply, smul_eq_mul]

/-- The actual first four original factors act on the genuine sparse physical column
with the source phases and its scalar one-half retained. -/
theorem generatedNinth_column_prefix_four_spin :
    (monsterSourcePermutationSpin 1 * monsterSourcePermutationSpin 0 *
      xiSpinHolomorph * monsterSourcePermutationSpin 1).val
        (nortonUIntegerEmbed (generatedNinthColumnInputInteger 1)) =
      (1 / 2 : ℝ) • nortonUIntegerEmbed (generatedNinthColumnSpinData 4) := by
  have h₁ : (monsterSourcePermutationSpin 1).val
      (nortonUIntegerEmbed (generatedNinthColumnInputInteger 1)) =
        nortonUIntegerEmbed (generatedNinthColumnSpinData 1) := by
    rw [← generatedNinth_column_initial_actual, generatedNinth_integer_permutation_embed,
      generatedNinth_column_packed_permutation_one_actual]
  have h₂ : xiSpinHolomorph.val (nortonUIntegerEmbed (generatedNinthColumnSpinData 1)) =
      (1 / 2 : ℝ) • nortonUIntegerEmbed (generatedNinthColumnSpinData 2) := by
    rw [nortonUIntegerXi_embed, generatedNinth_column_packed_xi_step_2_actual,
      embed_four, smul_smul]
    norm_num
  have h₃ : (monsterSourcePermutationSpin 0).val
      (nortonUIntegerEmbed (generatedNinthColumnSpinData 2)) =
        nortonUIntegerEmbed (generatedNinthColumnSpinData 3) := by
    rw [generatedNinth_integer_permutation_embed,
      generatedNinth_column_packed_permutation_3_actual]
  have h₄ : (monsterSourcePermutationSpin 1).val
      (nortonUIntegerEmbed (generatedNinthColumnSpinData 3)) =
        nortonUIntegerEmbed (generatedNinthColumnSpinData 4) := by
    rw [generatedNinth_integer_permutation_embed,
      generatedNinth_column_packed_permutation_4_actual]
  exact four_spin_states _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
