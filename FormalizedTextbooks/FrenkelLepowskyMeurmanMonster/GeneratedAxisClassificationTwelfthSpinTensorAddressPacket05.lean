/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinPauliFast

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCachedAddresses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinQuadraticFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinLabelMatrixFast

/-! Every compact monomial boundary source address for generator 5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_00 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨0 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨0 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_01 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨1 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨1 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_02 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨2 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨2 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_03 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨3 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨3 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_04 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨4 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨4 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_05 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨5 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨5 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_06 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨6 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨6 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_07 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨7 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨7 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_08 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨8 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨8 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_09 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨9 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨9 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_10 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨10 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨10 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_11 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨11 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨11 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_12 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨12 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨12 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_13 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨13 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨13 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_14 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨14 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨14 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Check every full coordinate in this bounded tensor packet.
private theorem block_15 : ∀ u : Fin 256,
    generatedTwelfthSpinTensorAddressCondition 5
      ⟨15 * 256 + u.val, by omega⟩ := by
  have hc : ∀ u : Fin 256,
    generatedTwelfthSpinTensorCachedAddressCondition 5
      ⟨15 * 256 + u.val, by omega⟩ := by
    dsimp only [generatedTwelfthSpinTensorCachedAddressCondition]
    simp_rw [generatedTwelfth_spin_label_right_inverse_fast,
      generatedTwelfth_spin_label_left_inverse_fast, generatedTwelfth_spin_quadratic_fast_sign,
      generatedTwelfth_spin_pauli_sign_fast]
    decide +kernel
  intro u
  exact generatedTwelfth_spin_tensor_address_of_cached _ _ (hc u)

set_option maxHeartbeats 8000000 in
-- Reindex the complete finite spin labels through independent bounded blocks.
/-- All 4096 original source spin labels retain both compact boundary signs and addresses. -/
theorem generatedTwelfth_spin_tensor_address_packet_05 :
    ∀ n : Fin 4096, generatedTwelfthSpinTensorAddressCondition 5 n := by
  have h : ∀ (b : Fin 16) (u : Fin 256),
      generatedTwelfthSpinTensorAddressCondition 5 ⟨b.val * 256 + u.val, by omega⟩ := by
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
  intro n
  let b : Fin 16 := ⟨n.val / 256, by omega⟩
  let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 256 + u.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp [b, u]
    omega
  exact he ▸ h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
