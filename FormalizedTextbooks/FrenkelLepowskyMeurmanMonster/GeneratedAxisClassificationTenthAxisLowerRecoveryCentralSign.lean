/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySignedAnchorGeneration

/-! The actual central basis code has the identity Conway projection and identity full-axis lift. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every coordinate of original code label 2048 is the true all-one Golay coordinate. -/
theorem generatedTenth_axis_lower_recovery_central_code : ∀ i : Fin 24,
    (generatedTenthAxisLowerRecoveryCode 2048).val i = 1 := by decide +kernel

/-- The original central code sign is literally the negative identity on the physical space. -/
theorem generatedTenth_axis_lower_recovery_central_sign_apply (x : Fin 24 → ℝ) :
    (golaySignIsometry (generatedTenthAxisLowerRecoveryCode 2048)).val x = -x := by
  ext i
  change qSign ((generatedTenthAxisLowerRecoveryCode 2048).val i) * x i = -x i
  rw [generatedTenth_axis_lower_recovery_central_code, qSign_one, neg_one_mul]

/-- The actual central basis sign belongs to the genuine original sign subgroup. -/
theorem generatedTenth_axis_lower_recovery_central_sign_mem :
    golaySignIsometry (generatedTenthAxisLowerRecoveryCode 2048) ∈ signsSubgroup :=
  Or.inr generatedTenth_axis_lower_recovery_central_sign_apply

/-- Actual standard-to-original conjugation preserves the true negative identity. -/
theorem generatedTenth_axis_lower_recovery_central_original_mem :
    generatedTenthE7OrbitConjugation
      (golaySignIsometry (generatedTenthAxisLowerRecoveryCode 2048)) ∈ signsSubgroup := by
  right
  intro x
  change generatedTenthE7OrbitTransport.val
    ((golaySignIsometry (generatedTenthAxisLowerRecoveryCode 2048)).val
      (generatedTenthE7OrbitTransport.val.symm x)) = -x
  rw [generatedTenth_axis_lower_recovery_central_sign_apply, map_neg,
    LinearEquiv.apply_symm_apply]

/-- The entire actual central basis projection is identity in the original Conway quotient. -/
theorem generatedTenth_axis_lower_recovery_central_projection :
    generatedTenthAxisLowerRecoveryOriginalProjection
      (golaySignIsometry (generatedTenthAxisLowerRecoveryCode 2048)) = 1 := by
  have h : generatedTenthE7OrbitConjugation
      (golaySignIsometry (generatedTenthAxisLowerRecoveryCode 2048)) ∈
      (QuotientGroup.mk' signsSubgroup).ker := by
    rw [QuotientGroup.ker_mk']
    exact generatedTenth_axis_lower_recovery_central_original_mem
  exact h

/-- Identity in the genuine original H group is the actual full-axis lift of the central value. -/
theorem generatedTenth_axis_lower_recovery_central_full_axis_lift :
    ∃ h : H, rhoLocal h generatedTenthAxis = generatedTenthAxis ∧
      projH h = generatedTenthAxisLowerRecoveryOriginalProjection
        (golaySignIsometry (generatedTenthAxisLowerRecoveryCode 2048)) := by
  refine ⟨1, ?_, ?_⟩
  · rw [map_one]
    rfl
  · rw [map_one, generatedTenth_axis_lower_recovery_central_projection]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
