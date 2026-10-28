/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthHighOddCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinSupportExact

/-! The actual outgoing tensor column combines a controlled old Y row and one high odd row. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual sixteenth tensor column with its original common denominator cleared. -/
def generatedSixthTensorColumn (t : SpinIndex) : ℝ :=
  32 * Real.sqrt 2 * (griessConwayEncode generatedSixthAxis).2.2 t 16

/-- The incoming odd-short contribution to that actual denominator-cleared column. -/
def generatedSixthTensorXContribution (t : SpinIndex) : ℝ :=
  32 * qSign (t 11) *
    (if (golayEncodedMask (spinDictionaryCode t).val).testBit (16 : Fin 24).val then -1 else 1) *
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (spinDictionaryCode t, 16)))

/-- The outgoing tensor column retains both original dictionary contributions. -/
theorem generatedSixth_tensor_column_coordinate (t : SpinIndex) :
    generatedSixthTensorColumn t =
      generatedSixthTensorXContribution t + generatedSixthTensorYContribution t 16 := by
  unfold generatedSixthTensorColumn
  rw [generatedSixthAxis_local_expression, generatedSixth_triality_tensor_coordinate]
  simp only [trialityYTensor, ite_true, mul_one]
  unfold generatedSixthTensorXContribution generatedSixthTensorYContribution
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- The original odd contribution retains exactly 1024 times its incoming coefficient square. -/
theorem generatedSixth_tensor_X_square (t : SpinIndex) :
    (generatedSixthTensorXContribution t) ^ 2 = 1024 *
      ((griessConwayEncode
        (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
          (Sum.inr (Sum.inr (spinDictionaryCode t, 16)))) ^ 2 := by
  unfold generatedSixthTensorXContribution
  rw [mul_pow, mul_pow, mul_pow, pow_two (qSign _), qSign_sq]
  split_ifs <;> ring

/-- All codes except the exceptional actual odd row contribute absolute value at most eight. -/
theorem generatedSixth_tensor_X_small (t : SpinIndex) (ht : spinDictionaryCode t ≠ 1010) :
    (generatedSixthTensorXContribution t) ^ 2 ≤ 64 := by
  rw [generatedSixth_tensor_X_square]
  have h := generatedSixth_middle_odd_sixteen_small (spinDictionaryCode t) ht
  linarith

/-- The original Y contribution has the same value on both members of each Ω pair. -/
theorem generatedSixth_tensor_Y_omega (t : SpinIndex) :
    generatedSixthTensorYContribution (t + Pi.single (11 : Fin 12) 1) 16 =
      generatedSixthTensorYContribution t 16 := by
  unfold generatedSixthTensorYContribution
  simp only [spinDictionaryCode_add_omega]

/-- The original odd contribution reverses its sign on the other member of each Ω pair. -/
theorem generatedSixth_tensor_X_omega (t : SpinIndex) :
    generatedSixthTensorXContribution (t + Pi.single (11 : Fin 12) 1) =
      -generatedSixthTensorXContribution t := by
  unfold generatedSixthTensorXContribution
  simp only [spinDictionaryCode_add_omega, Pi.add_apply, Pi.single_eq_same, qSign_add,
    qSign_one]
  ring

/-- Actual homogeneous Pauli equations put the high Ω coordinate inside the genuine spin support. -/
theorem generatedSixth_spin_high_square :
    (generatedSixthSpinState (golayLabelCoefficients 3058)) ^ 2 = (1 / 256 : ℝ) := by
  apply generatedSixth_spin_kernel_square_exact
  decide +kernel

/-- The original low/high difference at code 1010 has its exact nonzero square. -/
theorem generatedSixth_spin_high_difference_square :
    (generatedSixthSpinState (golayLabelCoefficients 1010) -
      generatedSixthSpinState (golayLabelCoefficients 3058)) ^ 2 = (1 / 256 : ℝ) := by
  have h := generatedSixth_spin_state_omega_product_zero (golayLabelCoefficients 1010)
  have ho : golayLabelCoefficients 1010 + Pi.single (11 : Fin 12) 1 =
      golayLabelCoefficients 3058 := by
    exact golayLabel_low_add_omega (1010 : Fin 2048)
  rw [ho] at h
  have hn : generatedSixthSpinState (golayLabelCoefficients 3058) ≠ 0 := by
    intro hn
    have he := generatedSixth_spin_high_square
    rw [hn] at he
    norm_num at he
  have hz := (mul_eq_zero.mp h).resolve_right hn
  rw [hz, zero_sub, neg_sq]
  exact generatedSixth_spin_high_square

/-- The old Y contribution on the exceptional Ω pair has absolute value exactly three. -/
theorem generatedSixth_tensor_Y_high_square :
    (generatedSixthTensorYContribution (golayLabelCoefficients 1010) 16) ^ 2 = 9 := by
  rw [generatedSixth_tensor_Y_state]
  have hl : (⟨(1010 : Fin 2048).val, by omega⟩ : Fin 4096) = 1010 := by
    apply Fin.ext
    norm_num
  have hd := spinDictionaryCode_low (1010 : Fin 2048)
  rw [hl] at hd
  simp only [hd]
  have hc : generatedSixthFrameVectorData 8 0 16 = -3 := by decide +kernel
  have hh : (⟨(1010 : Fin 2048).val + 2048, by omega⟩ : Fin 4096) = 3058 := by
    apply Fin.ext
    norm_num
  simp only [hc, hl, hh, Int.cast_neg, Int.cast_ofNat]
  change (-16 * (-3 : ℝ) * _ * _ *
    (generatedSixthSpinState (golayLabelCoefficients 1010) -
      generatedSixthSpinState (golayLabelCoefficients 3058))) ^ 2 = 9
  rw [mul_pow, mul_pow, mul_pow, mul_pow, generatedSixth_spin_high_difference_square,
    pow_two (qSign _), qSign_sq]
  split_ifs <;> norm_num

/-- The exceptional incoming odd row contributes absolute value exactly twenty-four. -/
theorem generatedSixth_tensor_X_high_square :
    (generatedSixthTensorXContribution (golayLabelCoefficients 1010)) ^ 2 = 576 := by
  rw [generatedSixth_tensor_X_square]
  have hl : (⟨(1010 : Fin 2048).val, by omega⟩ : Fin 4096) = 1010 := by
    apply Fin.ext
    norm_num
  have hd := spinDictionaryCode_low (1010 : Fin 2048)
  rw [hl] at hd
  rw [hd, generatedSixth_high_odd_coefficient]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
