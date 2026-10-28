/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinLabelXor

/-! Every individual Fourier source label, including all twelve original coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_00 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 0 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 0 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_01 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 1 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 1 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_02 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 2 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 2 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_03 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 3 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 3 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_04 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 4 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 4 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_05 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 5 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 5 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_06 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 6 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 6 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_07 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 7 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 7 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_08 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 8 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 8 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_09 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 9 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 9 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_10 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 10 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 10 n

set_option maxHeartbeats 8000000 in
-- Check every original Fourier address in the complete finite coordinate range.
private theorem coordinate_11 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorFourierAddressCondition 11 n := by
  intro n
  exact generatedTwelfth_spin_label_xor 11 n

/-- All individual Fourier source label changes are exact binary flips. -/
theorem generatedNinth_lower_spin_tensor_fourier_addresses :
    ∀ k n, generatedNinthLowerSpinTensorFourierAddressCondition k n := by
  intro k n
  fin_cases k
  · exact coordinate_00 n
  · exact coordinate_01 n
  · exact coordinate_02 n
  · exact coordinate_03 n
  · exact coordinate_04 n
  · exact coordinate_05 n
  · exact coordinate_06 n
  · exact coordinate_07 n
  · exact coordinate_08 n
  · exact coordinate_09 n
  · exact coordinate_10 n
  · exact coordinate_11 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
