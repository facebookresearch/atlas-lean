/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPartialSpinAnchors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPhaseModel

/-! The actual original eight-factor spin word has its exact signed scalar anchor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem word_association (p q x : SpinHolomorph) :
    x * (q * (x * (p * (q * (p * (x * p)))))) =
      x * q * x * p * q * p * x * p := by
  simp only [mul_assoc]

/-- The last original prefix is exactly the unchanged sixth middle spin state. -/
theorem generatedSixth_partial_state_final :
    generatedSixthPartialSpinState 8 = generatedSixthSpinState :=
  congrArg (fun s : SpinHolomorph => s.val (generatedOddSpinState 0 1 0))
    (word_association (monsterSourcePermutationSpin 0) (monsterSourcePermutationSpin 1)
      xiSpinHolomorph)

/-- The original spin-word coefficient at zero is positive one sixteenth. -/
theorem generatedSixth_spin_state_zero_value : generatedSixthSpinState 0 = 1 / 16 := by
  have h := generatedSixth_partial_anchor_values 8
  change generatedSixthPartialSpinState 8 (golayLabelCoefficients 0) = 1 / 16 at h
  rw [generatedSixth_partial_state_final] at h
  have hz : golayLabelCoefficients 0 = 0 := by decide +kernel
  rw [hz] at h
  exact h

/-- The finite signed phase model has the actual, proven scalar normalization. -/
theorem generatedSixth_spin_state_normalized_model (t : SpinIndex) :
    generatedSixthSpinState t = (1 / 16 : ℝ) * generatedSixthSpinPhaseModel t := by
  rw [generatedSixth_spin_phase_model, generatedSixth_spin_state_zero_value]
  exact mul_comm _ _

/-- The original integer circuit is the signed final affine phase vector times32. -/
theorem generatedSixth_spin_numerator_phase (n : Fin 4096) :
    generatedSixthIntegerSpinNumerator n = 32 * generatedSixthPartialPhaseInteger 8 n := by
  have hn := congrArg (fun f : SpinSpace => f (golayLabelCoefficients n))
    generatedSixth_integer_spin_numerator_actual
  have hp := congrArg (fun f : SpinSpace => f (golayLabelCoefficients n))
    (generatedSixth_partial_phase_embed 8)
  rw [generatedSixth_partial_state_final] at hp
  have ha := generatedSixth_partial_anchor_values 8
  change generatedSixthPartialSpinAnchor 8 = (1 / 16 : ℝ) at ha
  rw [ha] at hp
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff] at hn hp
  change generatedSixthSpinState (golayLabelCoefficients n) =
    (1 / 512 : ℝ) * (generatedSixthIntegerSpinNumerator n : ℝ) at hn
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_mul, Int.cast_ofNat]
  linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
