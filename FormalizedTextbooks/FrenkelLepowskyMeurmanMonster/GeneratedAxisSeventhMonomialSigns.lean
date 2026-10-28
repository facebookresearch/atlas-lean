/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatialCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionCode

/-! Actual original Golay signs fixing the seventh triangle projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original Golay sign preservation is exactly equality of its three actual triangle signs. -/
theorem generatedSeventh_sign_plane_fixed_iff (a : Fin 4096) :
    conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode a))
      generatedSeventhPlaneSupport = generatedSeventhPlaneSupport ↔
    golayEncoder (golayLabelCoefficients a) 16 = golayEncoder (golayLabelCoefficients a) 17 ∧
      golayEncoder (golayLabelCoefficients a) 16 = golayEncoder (golayLabelCoefficients a) 19 := by
  have hp (i j : Fin 24) : generatedSeventhPlaneSupport i j =
      if generatedSeventhTriangle i ∧ generatedSeventhTriangle j then
        if i = j then (2 : ℝ) else -1 else 0 := by
    change (generatedSeventhPlaneNumerator i j : ℝ) = _
    simp only [generatedSeventhPlaneNumerator]
    split_ifs <;> norm_num
  have he (i j : Fin 24) (hij : i ≠ j) (hi : generatedSeventhTriangle i)
      (hj : generatedSeventhTriangle j)
      (h : conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode a))
        generatedSeventhPlaneSupport = generatedSeventhPlaneSupport) :
      golayEncoder (golayLabelCoefficients a) i = golayEncoder (golayLabelCoefficients a) j := by
    have hentry := congrArg (fun M : Matrix (Fin 24) (Fin 24) ℝ => M i j) h
    rw [sourceGeneratedSign_matrix_apply, hp, ite_eq_left ⟨hi, hj⟩, ite_eq_right hij] at hentry
    have hs : qSign (golayEncoder (golayLabelCoefficients a) i +
        golayEncoder (golayLabelCoefficients a) j) = 1 := by linarith
    have hzero := (qSign_eq_one_iff _).mp hs
    have hbin : ∀ u v : ZMod 2, u + v = 0 ↔ u = v := by decide
    exact (hbin _ _).mp hzero
  constructor
  · intro h
    exact ⟨he 16 17 (by decide) (Or.inl rfl) (Or.inr (Or.inl rfl)) h,
      he 16 19 (by decide) (Or.inl rfl) (Or.inr (Or.inr rfl)) h⟩
  · rintro ⟨h17, h19⟩
    have ht (i : Fin 24) (hi : generatedSeventhTriangle i) :
        golayEncoder (golayLabelCoefficients a) i = golayEncoder (golayLabelCoefficients a) 16 := by
      rcases hi with rfl | rfl | rfl
      · rfl
      · exact h17.symm
      · exact h19.symm
    ext i j
    rw [sourceGeneratedSign_matrix_apply]
    by_cases htri : generatedSeventhTriangle i ∧ generatedSeventhTriangle j
    · rw [ht i htri.1, ht j htri.2, CharTwo.add_self_eq_zero, qSign_zero, one_mul]
    · rw [hp, ite_eq_right htri, mul_zero]

/-- Every actual original Golay sign fixes every genuine coordinate section projection. -/
theorem generatedSeventh_sign_coordinate_projection (a : Fin 4096) (c : Fin 24 → ZMod 2) :
    conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode a))
      (Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) =
        Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) := by
  ext i j
  rw [sourceGeneratedSign_matrix_apply]
  by_cases hij : i = j
  · subst j
    rw [CharTwo.add_self_eq_zero, qSign_zero, one_mul]
  · have hz : (Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1)) i j = 0 := by
      simp only [Matrix.diagonal_apply, ite_eq_right hij]
    rw [hz, mul_zero]

/-- Original Golay sign fixation of the actual seventh matrix has two binary constraints. -/
theorem generatedSeventh_sign_spatial_mem_iff (a : Fin 4096) :
    golaySignIsometry (sourceGeneratedSignCode a) ∈ generatedSeventhSpatialStabilizer ↔
    golayEncoder (golayLabelCoefficients a) 16 = golayEncoder (golayLabelCoefficients a) 17 ∧
      golayEncoder (golayLabelCoefficients a) 16 = golayEncoder (golayLabelCoefficients a) 19 := by
  change conwayMatrixAction _ (griessConwayEncode generatedSeventhAxis).1 =
    (griessConwayEncode generatedSeventhAxis).1 ↔ _
  rw [generatedSeventh_axis_matrix_section_plane_fixed_iff]
  have hs : golaySignIsometry (sourceGeneratedSignCode a) ∈
      generatedAxisE8SectionStabilizer (golayOctadWord generatedSeventhSectionOctad) := by
    rw [generatedAxisE8SectionStabilizer_mem]
    exact (generatedAxisE8_matrix_action_iff_section_stabilizer _ _).mp
      (generatedSeventh_sign_coordinate_projection a _)
  rw [and_iff_right hs, generatedSeventh_sign_plane_fixed_iff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
