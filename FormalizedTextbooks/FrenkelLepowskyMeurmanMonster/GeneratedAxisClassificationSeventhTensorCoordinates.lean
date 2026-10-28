/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhHighOddCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpinSupportExact

/-! The actual outgoing tensor column combines a controlled old Y row and one high odd row. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual sixteenth tensor column with its original common denominator cleared. -/
def generatedSeventhTensorColumn (t : SpinIndex) : ℝ :=
  32 * Real.sqrt 2 * (griessConwayEncode generatedSeventhAxis).2.2 t 16

/-- The incoming odd-short contribution to that actual denominator-cleared column. -/
def generatedSeventhTensorXContribution (t : SpinIndex) : ℝ :=
  32 * qSign (t 11) *
    (if (golayEncodedMask (spinDictionaryCode t).val).testBit (16 : Fin 24).val then -1 else 1) *
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (spinDictionaryCode t, 16)))

/-- The outgoing tensor column retains both original dictionary contributions. -/
theorem generatedSeventh_tensor_column_coordinate (t : SpinIndex) :
    generatedSeventhTensorColumn t =
      generatedSeventhTensorXContribution t + generatedSeventhTensorYContribution t 16 := by
  unfold generatedSeventhTensorColumn
  rw [generatedSeventhAxis_local_expression, generatedSeventh_triality_tensor_coordinate]
  simp only [trialityYTensor, ite_true, mul_one]
  unfold generatedSeventhTensorXContribution generatedSeventhTensorYContribution
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- The original odd contribution retains exactly 1024 times its incoming coefficient square. -/
theorem generatedSeventh_tensor_X_square (t : SpinIndex) :
    (generatedSeventhTensorXContribution t) ^ 2 = 1024 *
      ((griessConwayEncode
        (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.1
          (Sum.inr (Sum.inr (spinDictionaryCode t, 16)))) ^ 2 := by
  unfold generatedSeventhTensorXContribution
  rw [mul_pow, mul_pow, mul_pow, pow_two (qSign _), qSign_sq]
  split_ifs <;> ring

/-- All codes except the exceptional actual odd row contribute absolute value at most eight. -/
theorem generatedSeventh_tensor_X_small (t : SpinIndex) (ht : spinDictionaryCode t ≠ 1012) :
    (generatedSeventhTensorXContribution t) ^ 2 ≤ 64 := by
  rw [generatedSeventh_tensor_X_square]
  have h := generatedSeventh_middle_odd_sixteen_small (spinDictionaryCode t) ht
  linarith

/-- The original Y contribution has the same value on both members of each Ω pair. -/
theorem generatedSeventh_tensor_Y_omega (t : SpinIndex) :
    generatedSeventhTensorYContribution (t + Pi.single (11 : Fin 12) 1) 16 =
      generatedSeventhTensorYContribution t 16 := by
  unfold generatedSeventhTensorYContribution
  simp only [spinDictionaryCode_add_omega]

/-- The original odd contribution reverses its sign on the other member of each Ω pair. -/
theorem generatedSeventh_tensor_X_omega (t : SpinIndex) :
    generatedSeventhTensorXContribution (t + Pi.single (11 : Fin 12) 1) =
      -generatedSeventhTensorXContribution t := by
  unfold generatedSeventhTensorXContribution
  simp only [spinDictionaryCode_add_omega, Pi.add_apply, Pi.single_eq_same, qSign_add,
    qSign_one]
  ring

/-- Actual homogeneous Pauli equations put the high Ω coordinate inside the genuine spin support. -/
theorem generatedSeventh_spin_high_square :
    (generatedSeventhSpinState (golayLabelCoefficients 3060)) ^ 2 = (1 / 256 : ℝ) := by
  apply generatedSeventh_spin_kernel_square_exact
  decide +kernel

/-- The original low/high difference at code 1012 has its exact nonzero square. -/
theorem generatedSeventh_spin_high_difference_square :
    (generatedSeventhSpinState (golayLabelCoefficients 1012) -
      generatedSeventhSpinState (golayLabelCoefficients 3060)) ^ 2 = (1 / 256 : ℝ) := by
  have h := generatedSeventh_spin_state_omega_product_zero (golayLabelCoefficients 1012)
  have ho : golayLabelCoefficients 1012 + Pi.single (11 : Fin 12) 1 =
      golayLabelCoefficients 3060 := by
    exact golayLabel_low_add_omega (1012 : Fin 2048)
  rw [ho] at h
  have hn : generatedSeventhSpinState (golayLabelCoefficients 3060) ≠ 0 := by
    intro hn
    have he := generatedSeventh_spin_high_square
    rw [hn] at he
    norm_num at he
  have hz := (mul_eq_zero.mp h).resolve_right hn
  rw [hz, zero_sub, neg_sq]
  exact generatedSeventh_spin_high_square

/-- The old Y contribution on the exceptional Ω pair has absolute value exactly one. -/
theorem generatedSeventh_tensor_Y_high_square :
    (generatedSeventhTensorYContribution (golayLabelCoefficients 1012) 16) ^ 2 = 1 := by
  rw [generatedSeventh_tensor_Y_state]
  have hl : (⟨(1012 : Fin 2048).val, by omega⟩ : Fin 4096) = 1012 := by
    apply Fin.ext
    norm_num
  have hd := spinDictionaryCode_low (1012 : Fin 2048)
  rw [hl] at hd
  simp only [hd]
  have hc : generatedSeventhFrameVectorData 7 0 16 = 1 := by decide +kernel
  have hh : (⟨(1012 : Fin 2048).val + 2048, by omega⟩ : Fin 4096) = 3060 := by
    apply Fin.ext
    norm_num
  simp only [hc, hl, hh, Int.cast_one]
  change (-16 * (1 : ℝ) * _ * _ *
    (generatedSeventhSpinState (golayLabelCoefficients 1012) -
      generatedSeventhSpinState (golayLabelCoefficients 3060))) ^ 2 = 1
  rw [mul_pow, mul_pow, mul_pow, mul_pow, generatedSeventh_spin_high_difference_square,
    pow_two (qSign _), qSign_sq]
  split_ifs <;> norm_num

/-- The exceptional incoming odd row contributes absolute value exactly twenty-four. -/
theorem generatedSeventh_tensor_X_high_square :
    (generatedSeventhTensorXContribution (golayLabelCoefficients 1012)) ^ 2 = 576 := by
  rw [generatedSeventh_tensor_X_square]
  have hl : (⟨(1012 : Fin 2048).val, by omega⟩ : Fin 4096) = 1012 := by
    apply Fin.ext
    norm_num
  have hd := spinDictionaryCode_low (1012 : Fin 2048)
  rw [hl] at hd
  rw [hd, generatedSeventh_high_odd_coefficient]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
