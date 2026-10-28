/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinPauliState
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthHighOddPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary

/-! The exceptional middle odd row retains its original preferred-Q central phase. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem plus_source_Q :
    griessShortQ (Sum.inl (1, generatedSixthSourcePair 2)) =
      griessShortQ (Sum.inl (0, generatedSixthSourcePair 2)) *
        (qCentral 1 * generatedSixthSpinPauliInitial 11) := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [griessPairQ_translation, spinTranslation_mul, griessPairQ_translation]
    have h : spinTranslation (qCentral 1 * generatedSixthSpinPauliInitial 11) =
        Pi.single 11 1 := by
      ext i
      fin_cases i <;> decide +kernel
    rw [h]
    simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false, zero_add]
  · rw [griessPairQ_modulation, spinModulation_mul, griessPairQ_modulation]
    have h : spinModulation (qCentral 1 * generatedSixthSpinPauliInitial 11) = 0 := by
      ext i
      fin_cases i <;> decide +kernel
    rw [h, add_zero]
  · rw [griessShortQ_coeff]
    change 0 = (0 + toAdd (qCentral 1 * generatedSixthSpinPauliInitial 11).coeff) +
      spinDot (spinTranslation (griessShortQ (Sum.inl (0, generatedSixthSourcePair 2))))
        (spinModulation (qCentral 1 * generatedSixthSpinPauliInitial 11))
    rw [griessPairQ_translation]
    simp only [ite_true, spinDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero, zero_add]
    decide +kernel

private theorem plus_target_Q :
    griessShortQ (Sum.inl (0, generatedSixthTargetPair 2)) *
      (qCentral 1 * generatedSixthSpinPauliCache 11 8) =
        griessShortQ (Sum.inr (Sum.inr (1010, 16))) := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [spinTranslation_mul, griessPairQ_translation, griessOdd_translation]
    simp only [ite_true, zero_add]
    ext i
    fin_cases i <;> decide +kernel
  · rw [spinModulation_mul, griessPairQ_modulation,
      (generatedSixth_pair_syndrome_certificate 2).2, griessOdd_modulation]
    ext i
    fin_cases i <;> decide +kernel
  · rw [griessShortQ_coeff]
    change (0 + toAdd (qCentral 1 * generatedSixthSpinPauliCache 11 8).coeff) +
      spinDot (spinTranslation (griessShortQ (Sum.inl (0, generatedSixthTargetPair 2))))
        (spinModulation (qCentral 1 * generatedSixthSpinPauliCache 11 8)) = 0
    rw [griessPairQ_translation]
    simp only [ite_true, spinDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero, zero_add]
    decide +kernel

/-- The exceptional high source pair has full preferred-Q image with central sign zero. -/
theorem generatedSixth_high_odd_preferred_transport :
    spinConjugation generatedSixthLocalFiber.val.1
      (griessShortQ (Sum.inl (1, generatedSixthSourcePair 2))) =
        griessShortQ (Sum.inr (Sum.inr (1010, 16))) := by
  rw [plus_source_Q, map_mul, generatedSixth_preferred_pair_transport, map_mul,
    spinConjugation_central, generatedSixth_spin_pauli_transport, plus_target_Q]

/-- The exceptional source pair reaches actual odd code 1010 and coordinate sixteen. -/
theorem generatedSixth_high_odd_permutation :
    griessShortPermutation generatedSixthLocalFiber.val.2
      (Sum.inl (1, generatedSixthSourcePair 2)) = Sum.inr (Sum.inr (1010, 16)) := by
  have hb := griessShortQ_image_base generatedSixthLocalFiber
    (Sum.inl (1, generatedSixthSourcePair 2))
  rw [generatedSixth_high_odd_preferred_transport] at hb
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact (congrArg Multiplicative.toAdd hb).symm

/-- The high odd coefficient is exactly positive three quarters in the original middle vector. -/
theorem generatedSixth_high_odd_coefficient :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inr (1010, 16))) = (3 / 4 : ℝ) := by
  rw [generatedFourth_local_short, ← generatedSixth_high_odd_permutation,
    localShortOperator_image]
  have hp : localShortPhase generatedSixthLocalFiber
      (Sum.inl (1, generatedSixthSourcePair 2)) = 0 := by
    unfold localShortPhase
    rw [generatedSixth_high_odd_preferred_transport, griessShortQ_coeff]
  rw [hp, qSign_zero, one_mul, generatedSixth_original_pair_coordinate,
    (generatedSixth_pair_coordinate_certificate 2).1]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
