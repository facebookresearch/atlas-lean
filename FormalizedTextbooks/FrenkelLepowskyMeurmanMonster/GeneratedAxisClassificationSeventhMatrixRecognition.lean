/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMatrixSupport

/-! Actual matrix fixation is exactly preservation of its two intrinsic spatial supports. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual two-root and six-dimensional supports completely characterize matrix fixation. -/
theorem generatedSeventh_axis_matrix_support_fixed_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedSeventhAxis).1 =
        (griessConwayEncode generatedSeventhAxis).1 ↔
      conwayMatrixAction g generatedSeventhPlaneSupport = generatedSeventhPlaneSupport ∧
        conwayMatrixAction g generatedSeventhSixSupport = generatedSeventhSixSupport := by
  rw [generatedSeventh_axis_matrix, generatedSeventh_matrix_numerator_real, map_smul]
  have hn : conwayMatrixAction g generatedSeventhMatrixIntegerReal =
      generatedSeventhMatrixIntegerReal ↔
      conwayMatrixAction g generatedSeventhPlaneSupport = generatedSeventhPlaneSupport ∧
        conwayMatrixAction g generatedSeventhSixSupport = generatedSeventhSixSupport := by
    constructor
    · intro hN
      constructor
      · have h := congrArg (conwayMatrixAction g) generatedSeventh_plane_polynomial_real
        rw [map_add, map_sub, map_smul, map_smul, conwayMatrixAction_mul,
          conwayMatrixAction_one, hN, map_smul, generatedSeventh_plane_polynomial_real] at h
        exact (smul_right_injective _ (by norm_num : (16 : ℝ) ≠ 0)) h.symm
      · have h := congrArg (conwayMatrixAction g) generatedSeventh_six_polynomial_real
        rw [map_add, map_sub, map_smul, map_smul, conwayMatrixAction_mul,
          conwayMatrixAction_one, hN, map_smul, generatedSeventh_six_polynomial_real] at h
        exact (smul_right_injective _ (by norm_num : (32 : ℝ) ≠ 0)) h.symm
    · rintro ⟨hP, hS⟩
      have h := congrArg (conwayMatrixAction g) generatedSeventh_support_reconstruction_real
      rw [map_smul, map_sub, map_add, map_smul, map_smul, map_smul,
        conwayMatrixAction_one, hP, hS, ← generatedSeventh_support_reconstruction_real] at h
      exact (smul_right_injective _ (by norm_num : (3 : ℝ) ≠ 0)) h
  exact (smul_right_injective _ (by norm_num : (1 / 32 : ℝ) ≠ 0)).eq_iff.trans hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
