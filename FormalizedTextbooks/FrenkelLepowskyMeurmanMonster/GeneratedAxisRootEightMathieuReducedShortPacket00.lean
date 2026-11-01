/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBalancedMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinParityCircuit

/-! Complete original signed-short fixer certificates; source zeros are retained. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_000 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨0 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_001 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨256 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_002 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨512 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_003 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨768 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_004 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨1024 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_005 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨1280 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_006 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨1536 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_007 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨1792 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_008 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨2048 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_009 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨2304 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_010 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨2560 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_011 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨2816 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_012 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨3072 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_013 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨3328 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_014 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨3584 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

set_option maxHeartbeats 64000000 in
private theorem short_fixer_block_015 :
    ∀ g : Fin 4, ∀ u : Fin 256, generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨3840 + u.val, by omega⟩) := by
  unfold generatedRootEightMathieuReducedShortSupportCondition generatedRootEightMathieuReducedShortPackedCondition
  simp_rw [← generatedNinth_lower_spin_short_balanced_mask_actual,
    ← generatedNinth_lower_spin_circuit_q_mask_central]
  decide +kernel

/-- Complete original phases and coefficients for all nonzero sources in this interval. -/
theorem generatedRootEight_mathieu_reduced_short_packet_00 (g : Fin 4) (n : Fin 4096) :
    generatedRootEightMathieuReducedShortSupportCondition g
      (generatedNinthLowerSpinShortIndex ⟨0+n.val, by omega⟩) := by
  by_cases h0 : n.val < 256
  · let u : Fin 256 := ⟨n.val-0, by omega⟩
    have he : (⟨0+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_000 g u
    rw [he] at h
    exact h
  by_cases h1 : n.val < 512
  · let u : Fin 256 := ⟨n.val-256, by omega⟩
    have he : (⟨256+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_001 g u
    rw [he] at h
    exact h
  by_cases h2 : n.val < 768
  · let u : Fin 256 := ⟨n.val-512, by omega⟩
    have he : (⟨512+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_002 g u
    rw [he] at h
    exact h
  by_cases h3 : n.val < 1024
  · let u : Fin 256 := ⟨n.val-768, by omega⟩
    have he : (⟨768+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_003 g u
    rw [he] at h
    exact h
  by_cases h4 : n.val < 1280
  · let u : Fin 256 := ⟨n.val-1024, by omega⟩
    have he : (⟨1024+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_004 g u
    rw [he] at h
    exact h
  by_cases h5 : n.val < 1536
  · let u : Fin 256 := ⟨n.val-1280, by omega⟩
    have he : (⟨1280+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_005 g u
    rw [he] at h
    exact h
  by_cases h6 : n.val < 1792
  · let u : Fin 256 := ⟨n.val-1536, by omega⟩
    have he : (⟨1536+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_006 g u
    rw [he] at h
    exact h
  by_cases h7 : n.val < 2048
  · let u : Fin 256 := ⟨n.val-1792, by omega⟩
    have he : (⟨1792+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_007 g u
    rw [he] at h
    exact h
  by_cases h8 : n.val < 2304
  · let u : Fin 256 := ⟨n.val-2048, by omega⟩
    have he : (⟨2048+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_008 g u
    rw [he] at h
    exact h
  by_cases h9 : n.val < 2560
  · let u : Fin 256 := ⟨n.val-2304, by omega⟩
    have he : (⟨2304+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_009 g u
    rw [he] at h
    exact h
  by_cases h10 : n.val < 2816
  · let u : Fin 256 := ⟨n.val-2560, by omega⟩
    have he : (⟨2560+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_010 g u
    rw [he] at h
    exact h
  by_cases h11 : n.val < 3072
  · let u : Fin 256 := ⟨n.val-2816, by omega⟩
    have he : (⟨2816+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_011 g u
    rw [he] at h
    exact h
  by_cases h12 : n.val < 3328
  · let u : Fin 256 := ⟨n.val-3072, by omega⟩
    have he : (⟨3072+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_012 g u
    rw [he] at h
    exact h
  by_cases h13 : n.val < 3584
  · let u : Fin 256 := ⟨n.val-3328, by omega⟩
    have he : (⟨3328+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_013 g u
    rw [he] at h
    exact h
  by_cases h14 : n.val < 3840
  · let u : Fin 256 := ⟨n.val-3584, by omega⟩
    have he : (⟨3584+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
      apply Fin.ext
      dsimp [u]
      try omega
    have h := short_fixer_block_014 g u
    rw [he] at h
    exact h
  let u : Fin 256 := ⟨n.val-3840, by omega⟩
  have he : (⟨3840+u.val, by omega⟩ : Fin 98280) =
        ⟨0+n.val, by omega⟩ := by
    apply Fin.ext
    dsimp [u]
    try omega
  have h := short_fixer_block_015 g u
  rw [he] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
