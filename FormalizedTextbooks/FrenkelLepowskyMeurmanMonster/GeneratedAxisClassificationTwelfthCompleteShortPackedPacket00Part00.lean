/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortPackedData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthShortThetaCachedMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastQMaskCentral

/-! Exact full preferred-short Q images and signed coefficients for a bounded original row
packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_00 : ∀ u : Fin 1024,
    if h : 0 * 8192 + 0 * 1024 + u.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0
        ⟨0 * 8192 + 0 * 1024 + u.val, h⟩ else True := by
  unfold generatedTwelfthCompleteShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central,
    ← generatedTwelfth_short_theta_cached_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_01 : ∀ u : Fin 1024,
    if h : 0 * 8192 + 1 * 1024 + u.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0
        ⟨0 * 8192 + 1 * 1024 + u.val, h⟩ else True := by
  unfold generatedTwelfthCompleteShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central,
    ← generatedTwelfth_short_theta_cached_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_02 : ∀ u : Fin 1024,
    if h : 0 * 8192 + 2 * 1024 + u.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0
        ⟨0 * 8192 + 2 * 1024 + u.val, h⟩ else True := by
  unfold generatedTwelfthCompleteShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central,
    ← generatedTwelfth_short_theta_cached_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_03 : ∀ u : Fin 1024,
    if h : 0 * 8192 + 3 * 1024 + u.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0
        ⟨0 * 8192 + 3 * 1024 + u.val, h⟩ else True := by
  unfold generatedTwelfthCompleteShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central,
    ← generatedTwelfth_short_theta_cached_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_04 : ∀ u : Fin 1024,
    if h : 0 * 8192 + 4 * 1024 + u.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0
        ⟨0 * 8192 + 4 * 1024 + u.val, h⟩ else True := by
  unfold generatedTwelfthCompleteShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central,
    ← generatedTwelfth_short_theta_cached_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_05 : ∀ u : Fin 1024,
    if h : 0 * 8192 + 5 * 1024 + u.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0
        ⟨0 * 8192 + 5 * 1024 + u.val, h⟩ else True := by
  unfold generatedTwelfthCompleteShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central,
    ← generatedTwelfth_short_theta_cached_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_06 : ∀ u : Fin 1024,
    if h : 0 * 8192 + 6 * 1024 + u.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0
        ⟨0 * 8192 + 6 * 1024 + u.val, h⟩ else True := by
  unfold generatedTwelfthCompleteShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central,
    ← generatedTwelfth_short_theta_cached_actual]
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Bound the exact vector, central phase, and coefficient check to 1,024 actual coordinates.
private theorem block_07 : ∀ u : Fin 1024,
    if h : 0 * 8192 + 7 * 1024 + u.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0
        ⟨0 * 8192 + 7 * 1024 + u.val, h⟩ else True := by
  unfold generatedTwelfthCompleteShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_fast_q_mask_central,
    ← generatedTwelfth_short_theta_cached_actual]
  decide +kernel

/-- Every actual preferred coordinate in this bounded packet has its full signed Q image. -/
theorem generatedTwelfth_complete_short_packed_packet_00_part_00 : ∀ a : Fin 8192,
    if h : 0 * 8192 + a.val < 98280 then
      generatedTwelfthCompleteShortPackedCondition 0 ⟨0 * 8192 + a.val, h⟩ else True := by
  have h : ∀ (b : Fin 8) (u : Fin 1024),
      if hn : 0 * 8192 + b.val * 1024 + u.val < 98280 then
        generatedTwelfthCompleteShortPackedCondition 0
          ⟨0 * 8192 + b.val * 1024 + u.val, hn⟩ else True := by
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
  intro a
  let b : Fin 8 := ⟨a.val / 1024, by omega⟩
  let u : Fin 1024 := ⟨a.val % 1024, Nat.mod_lt _ (by decide)⟩
  have hn : b.val * 1024 + u.val = a.val := by
    dsimp [b, u]
    omega
  simpa only [Nat.add_assoc, hn] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
