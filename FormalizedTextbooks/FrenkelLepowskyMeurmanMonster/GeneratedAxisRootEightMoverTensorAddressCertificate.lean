/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorCachedAddresses

/-! All original monomial source addresses, phases and central signs are checked. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_00 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨0 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨0 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_01 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨1 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨1 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_02 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨2 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨2 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_03 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨3 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨3 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_04 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨4 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨4 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_05 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨5 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨5 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_06 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨6 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨6 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_07 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨7 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨7 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_08 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨8 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨8 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_09 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨9 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨9 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_10 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨10 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨10 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_11 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨11 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨11 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_12 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨12 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨12 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_13 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨13 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨13 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_14 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨14 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨14 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check one bounded block of all original monomial labels and phases.
private theorem block_15 : ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨15 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
      generatedRootEightMoverTensorCachedAddressCondition
        ⟨15 * 256 + u.val, by omega⟩ := by
    unfold generatedRootEightMoverTensorCachedAddressCondition
    simp_rw [generatedTwelfth_spin_pauli_sign_fast,
      generatedNinth_lower_spin_quadratic_fast_sign,
      generatedRootEight_mover_tensor_right_inverse_fast,
      generatedRootEight_mover_tensor_left_inverse_fast]
    decide +kernel
  intro u
  exact generatedRootEight_mover_tensor_address_of_cached _ (hc u)

/-- Every complete bounded block has its original full coordinate certificate. -/
theorem generatedRootEight_mover_tensor_addresses_blocks : ∀ b : Fin 16, ∀ u : Fin 256,
    generatedRootEightMoverTensorAddressCondition ⟨b.val * 256 + u.val, by omega⟩ := by
  intro b u
  fin_cases b
  · exact block_00 u
  · exact block_01 u
  · exact block_02 u
  · exact block_03 u
  · exact block_04 u
  · exact block_05 u
  · exact block_06 u
  · exact block_07 u
  · exact block_08 u
  · exact block_09 u
  · exact block_10 u
  · exact block_11 u
  · exact block_12 u
  · exact block_13 u
  · exact block_14 u
  · exact block_15 u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
