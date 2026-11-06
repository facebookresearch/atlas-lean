/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ProjectionRecognition

/-! The recovered projection is transported to an actual coordinate-octad projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual increasing Golay octad catalogue entry of the destination support. -/
def generatedNinthSectionOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨generatedNinthSectionCode, generatedNinth_section_code_mem⟩

/-- The actual destination octad retains the exact original code label. -/
theorem generatedNinth_section_octad_label :
    golayOctadLabel generatedNinthSectionOctad = generatedNinthSectionCode := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨generatedNinthSectionCode, generatedNinth_section_code_mem⟩)

/-- The original transported short directions as real physical rows. -/
def generatedNinthSectionRootMatrix : Matrix (Fin 8) (Fin 24) ℝ :=
  fun r i => (generatedNinthSectionRootCoordinates r i : ℝ)

/-- The actual destination coordinate-octad projection. -/
def generatedNinthSectionProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.diagonal (fun i => if golayOctadWord generatedNinthSectionOctad i = 0 then 0 else 1)

/-- The original transported short outers recover the actual coordinate projection. -/
theorem generatedNinth_section_projection_outer :
    (1 / 2 : ℝ) •
      (generatedNinthSectionRootMatrix.transpose * generatedNinthSectionRootMatrix) =
        generatedNinthSectionProjection := by
  ext i j
  have h : (∑ r : Fin 8, (generatedNinthSectionRootCoordinates r i : ℝ) *
      (generatedNinthSectionRootCoordinates r j : ℝ)) =
        if i = j ∧ (golayEncodedMask generatedNinthSectionCode.val).testBit i.val = true
          then 2 else 0 := by
    exact_mod_cast generatedNinth_section_root_outer i j
  have hs : golayOctadWord generatedNinthSectionOctad i ≠ 0 ↔
      (golayEncodedMask generatedNinthSectionCode.val).testBit i.val = true := by
    simp only [golayOctadWord_ne_zero_iff, golayOctadSupport, golayMaskSupport,
      Finset.mem_filter, Finset.mem_univ, true_and, generatedNinth_section_octad_label]
  simp only [← hs] at h
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    generatedNinthSectionRootMatrix, generatedNinthSectionProjection, Matrix.diagonal_apply]
  rw [h]
  by_cases he : i = j
  · subst j
    by_cases hc : golayOctadWord generatedNinthSectionOctad i = 0 <;> norm_num [hc]
  · simp only [he, false_and, ite_false, mul_zero]

/-- The literal lattice matrix sends the whole eight-direction embedding
to its original certificate. -/
theorem generatedNinth_section_root_matrix :
    leechIsomMatrix generatedNinthSectionTransport * generatedNinthLowRootMatrix.transpose =
      generatedNinthSectionRootMatrix.transpose := by
  ext i r
  change (leechIsomMatrix generatedNinthSectionTransport *ᵥ generatedNinthLowRootMatrix r) i = _
  rw [leechIsomMatrix_mulVec, generatedNinth_section_root_action]
  rfl

/-- The actual source spatial word transports the recovered projection to a genuine octad. -/
theorem generatedNinth_section_projection_transport :
    conwayMatrixAction generatedNinthSectionTransport generatedNinthLowProjection =
      generatedNinthSectionProjection := by
  rw [conwayMatrixAction_eq_conjugate, generatedNinthLowProjection]
  calc
    _ = (1 / 2 : ℝ) •
        ((leechIsomMatrix generatedNinthSectionTransport *
          generatedNinthLowRootMatrix.transpose) *
            (leechIsomMatrix generatedNinthSectionTransport *
              generatedNinthLowRootMatrix.transpose).transpose) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = _ := by
      rw [generatedNinth_section_root_matrix, Matrix.transpose_transpose,
        generatedNinth_section_projection_outer]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
