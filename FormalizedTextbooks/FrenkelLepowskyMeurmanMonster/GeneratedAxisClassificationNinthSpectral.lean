/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The complete original matrix has genuine eigenspaces of dimensions eight and sixteen. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual upper physical subspace is the kernel of the eight-direction coordinate map. -/
def generatedNinthHighSpace : Submodule ℝ (Fin 24 → ℝ) :=
  LinearMap.ker (Matrix.toLin' generatedNinthLowRootMatrix)

/-- The original projection fixes the full eight-direction embedding. -/
theorem generatedNinth_low_projection_embedding :
    generatedNinthLowProjection * generatedNinthLowRootMatrix.transpose =
      generatedNinthLowRootMatrix.transpose := by
  rw [generatedNinthLowProjection, Matrix.smul_mul, Matrix.mul_assoc,
    generatedNinth_low_root_real_gram, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  norm_num

/-- Every vector in the actual lower subspace is fixed by the recovered projection. -/
theorem generatedNinth_low_projection_mem (v : Fin 24 → ℝ)
    (hv : v ∈ generatedNinthLowSpace) : generatedNinthLowProjection *ᵥ v = v := by
  obtain ⟨w, hw⟩ := hv
  change generatedNinthLowRootMatrix.transpose *ᵥ w = v at hw
  rw [← hw, Matrix.mulVec_mulVec, generatedNinth_low_projection_embedding]

/-- The original eight-direction coordinate map is onto its entire real target. -/
theorem generatedNinth_low_coordinate_surjective :
    Function.Surjective (Matrix.toLin' generatedNinthLowRootMatrix) := by
  intro v
  refine ⟨(1 / 2 : ℝ) • (generatedNinthLowRootMatrix.transpose *ᵥ v), ?_⟩
  change generatedNinthLowRootMatrix *ᵥ
    ((1 / 2 : ℝ) • (generatedNinthLowRootMatrix.transpose *ᵥ v)) = v
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, generatedNinth_low_root_real_gram,
    Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
  norm_num

/-- The complementary actual real subspace has dimension exactly sixteen. -/
theorem generatedNinth_high_space_finrank :
    Module.finrank ℝ generatedNinthHighSpace = 16 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Matrix.toLin' generatedNinthLowRootMatrix)
  rw [LinearMap.range_eq_top.mpr generatedNinth_low_coordinate_surjective] at h
  simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h
  change 8 + Module.finrank ℝ generatedNinthHighSpace = 24 at h
  omega

/-- Every actual lower vector is an eigenvector with eigenvalue one quarter. -/
theorem generatedNinth_low_eigenvector (v : Fin 24 → ℝ) (hv : v ∈ generatedNinthLowSpace) :
    (griessConwayEncode generatedNinthAxis).1 *ᵥ v = (1 / 4 : ℝ) • v := by
  rw [generatedNinth_matrix_projection, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, generatedNinth_low_projection_mem v hv]
  module

/-- Every actual upper vector is an eigenvector with eigenvalue three eighths. -/
theorem generatedNinth_high_eigenvector (v : Fin 24 → ℝ) (hv : v ∈ generatedNinthHighSpace) :
    (griessConwayEncode generatedNinthAxis).1 *ᵥ v = (3 / 8 : ℝ) • v := by
  have hzero : generatedNinthLowRootMatrix *ᵥ v = 0 := hv
  have hp : generatedNinthLowProjection *ᵥ v = 0 := by
    rw [generatedNinthLowProjection, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hzero]
    simp
  rw [generatedNinth_matrix_projection, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, hp, smul_zero, sub_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
