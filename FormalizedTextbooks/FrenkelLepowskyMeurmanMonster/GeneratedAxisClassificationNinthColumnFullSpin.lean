/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPrefixFour
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedPermutation7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnPackedXi9

/-! All nine literal original factors have their exact signed physical-column spin state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem embed_scale (a : ℤ) (v : NortonUIntegerVector) :
    nortonUIntegerEmbed (fun n => a * v n) = (a : ℝ) • nortonUIntegerEmbed v := by
  ext t
  simp only [nortonUIntegerEmbed, Int.cast_mul, Pi.smul_apply, smul_eq_mul]

private theorem xi_states (a : ℤ) (v w : NortonUIntegerVector)
    (h : nortonUIntegerXi v = fun n => a * w n) :
    xiSpinHolomorph.val (nortonUIntegerEmbed v) =
      ((a : ℝ) / 8) • nortonUIntegerEmbed w := by
  rw [nortonUIntegerXi_embed, h, embed_scale, smul_smul]
  congr 1
  ring

private theorem suffix_states (p₀ p₁ x : SpinHolomorph)
    (v₀ v₄ v₅ v₆ v₇ v₈ v₉ : SpinSpace)
    (h₄ : (p₁ * p₀ * x * p₁).val v₀ = (1 / 2 : ℝ) • v₄)
    (h₅ : x.val v₄ = (1 / 4 : ℝ) • v₅) (h₆ : p₀.val v₅ = v₆)
    (h₇ : p₁.val v₆ = v₇) (h₈ : x.val v₇ = (2 : ℝ) • v₈)
    (h₉ : x.val v₈ = v₉) :
    (x * x * p₁ * p₀ * x * (p₁ * p₀ * x * p₁)).val v₀ =
      (1 / 4 : ℝ) • v₉ := by
  change x.val (x.val (p₁.val (p₀.val (x.val
    ((p₁ * p₀ * x * p₁).val v₀))))) = _
  rw [h₄]
  simp only [h₅, h₆, h₇, h₈, h₉, map_smul, smul_smul]
  norm_num

/-- The entire actual ninth spin word has its source state and exact scalar one-quarter. -/
theorem generatedNinth_column_full_spin :
    generatedNinthLocalFiber.val.1.val
        (nortonUIntegerEmbed (generatedNinthColumnInputInteger 1)) =
      (1 / 4 : ℝ) • nortonUIntegerEmbed (generatedNinthColumnSpinData 9) := by
  have h₅ : xiSpinHolomorph.val (nortonUIntegerEmbed (generatedNinthColumnSpinData 4)) =
      (1 / 4 : ℝ) • nortonUIntegerEmbed (generatedNinthColumnSpinData 5) := by
    simpa only [show ((2 : ℤ) : ℝ) / 8 = 1 / 4 by norm_num] using
      xi_states 2 _ _ generatedNinth_column_packed_xi_step_5_actual
  have h₆ : (monsterSourcePermutationSpin 0).val
      (nortonUIntegerEmbed (generatedNinthColumnSpinData 5)) =
        nortonUIntegerEmbed (generatedNinthColumnSpinData 6) := by
    rw [generatedNinth_integer_permutation_embed,
      generatedNinth_column_packed_permutation_6_actual]
  have h₇ : (monsterSourcePermutationSpin 1).val
      (nortonUIntegerEmbed (generatedNinthColumnSpinData 6)) =
        nortonUIntegerEmbed (generatedNinthColumnSpinData 7) := by
    rw [generatedNinth_integer_permutation_embed,
      generatedNinth_column_packed_permutation_7_actual]
  have h₈ : xiSpinHolomorph.val (nortonUIntegerEmbed (generatedNinthColumnSpinData 7)) =
      (2 : ℝ) • nortonUIntegerEmbed (generatedNinthColumnSpinData 8) := by
    simpa only [show ((16 : ℤ) : ℝ) / 8 = 2 by norm_num] using
      xi_states 16 _ _ generatedNinth_column_packed_xi_step_8_actual
  have h₉ : xiSpinHolomorph.val (nortonUIntegerEmbed (generatedNinthColumnSpinData 8)) =
      nortonUIntegerEmbed (generatedNinthColumnSpinData 9) := by
    simpa only [show ((8 : ℤ) : ℝ) / 8 = 1 by norm_num, one_smul] using
      xi_states 8 _ _ generatedNinth_column_packed_xi_step_9_actual
  have hf : generatedNinthLocalFiber.val.1 =
      xiSpinHolomorph * xiSpinHolomorph * monsterSourcePermutationSpin 1 *
        monsterSourcePermutationSpin 0 * xiSpinHolomorph * monsterSourcePermutationSpin 1 *
        monsterSourcePermutationSpin 0 * xiSpinHolomorph * monsterSourcePermutationSpin 1 := rfl
  rw [hf]
  simpa only [mul_assoc] using suffix_states _ _ _ _ _ _ _ _ _ _
    generatedNinth_column_prefix_four_spin h₅ h₆ h₇ h₈ h₉

/-- The integer word's original denominator4096 matches exactly1024 times the certified state. -/
theorem generatedNinth_column_full_integer (n : Fin 4096) :
    generatedNinthIntegerSpin (generatedNinthColumnInputInteger 1) n =
      1024 * generatedNinthColumnSpinData 9 n := by
  have h := generatedNinth_column_full_spin
  rw [generatedNinth_integer_spin_embed] at h
  have hn := congrArg (fun v : SpinSpace => v (golayLabelCoefficients n)) h
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff] at hn
  have he : (generatedNinthIntegerSpin (generatedNinthColumnInputInteger 1) n : ℝ) =
      (1024 : ℝ) * (generatedNinthColumnSpinData 9 n : ℝ) := by linarith only [hn]
  exact_mod_cast he

/-- The actual middle tensor column retains its complete original word and denominator32√2. -/
theorem generatedNinth_middle_column_full (t : SpinIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.2 t 1 =
        (generatedNinthColumnSpinData 9 (nortonUIntegerLabel t) : ℝ) /
          (32 * Real.sqrt 2) := by
  rw [generatedNinth_middle_column_integer, generatedNinth_column_full_integer]
  simp only [Int.cast_mul, Int.cast_ofNat]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
