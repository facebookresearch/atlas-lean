/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhSpatialSection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SectionStabilizerCount

/-! The recovered actual section is an original integral E8 section under the genuine Xi. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original octad recovered after the genuine Xi action. -/
def generatedEleventhSectionOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm ⟨1345, by decide +kernel⟩

/-- The catalogue address is the original Golay encoder label. -/
theorem generatedEleventh_section_octad_label :
    golayOctadLabel generatedEleventhSectionOctad = 1345 :=
  congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨1345, by decide +kernel⟩)

/-- All physical octad coordinates agree with the original Golay encoder. -/
theorem generatedEleventh_section_octad_support (i : Fin 24) :
    golayOctadWord generatedEleventhSectionOctad i = 0 ↔
      Nat.testBit 0x22e122 i.val = false := by
  rw [golayOctadWord, generatedEleventh_section_octad_label, golayLabelEncoder_boolean]
  fin_cases i <;> decide +kernel

/-- The actual original spatial Xi has precisely its existing integer numerator. -/
theorem generatedEleventh_xi_physical_matrix :
    leechIsomMatrix co1XiIsometry =
      (1 / 2 : ℝ) • co1XiNumerator.map (Int.castRingHom ℝ) := by
  ext i j
  change xiSpinLocalFiber.val.2.val (Pi.single j 1) i = _
  rw [generatedFifth_xi_spatial_unit]
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  change (co1XiNumerator i j : ℝ) / 2 = (1 / 2 : ℝ) * (co1XiNumerator i j : ℝ)
  ring

/-- The real coordinate projection onto the genuine original octad. -/
def generatedEleventhOctadProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.diagonal (fun i => if Nat.testBit 0x22e122 i.val then 1 else 0)

/-- The original integer Xi conjugation is the exact real physical projection equation. -/
theorem generatedEleventh_section_xi_real :
    co1XiNumerator.map (Int.castRingHom ℝ) *
      generatedEleventhSectionInteger.map (Int.castRingHom ℝ) *
      (co1XiNumerator.map (Int.castRingHom ℝ)).transpose =
        (16 : ℝ) • generatedEleventhOctadProjection := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix generatedEleventh_section_xi_integer
  simp only [map_mul, map_nsmul] at h
  change co1XiNumerator.map (Int.castRingHom ℝ) *
      generatedEleventhSectionInteger.map (Int.castRingHom ℝ) *
      (co1XiNumerator.transpose.map (Int.castRingHom ℝ)) = _ at h
  rw [Matrix.transpose_map] at h
  convert h using 1
  ext i j
  simp only [generatedEleventhOctadProjection, Matrix.smul_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    cases hb : Nat.testBit 0x22e122 i.val <;> simp [nsmul_eq_mul, hb]
  · simp [hij]

/-- The actual original Xi sends the recovered spatial section to its genuine octad section. -/
theorem generatedEleventh_section_xi_actual :
    conwayMatrixAction co1XiIsometry generatedEleventhCoordinateSection =
      generatedEleventhOctadProjection := by
  rw [conwayMatrixAction_eq_conjugate, generatedEleventh_xi_physical_matrix,
    generatedEleventhCoordinateSection, Matrix.transpose_smul]
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, generatedEleventh_section_xi_real]
  simp only [smul_smul]
  norm_num

/-- The recovered coordinate projector is exactly the genuine octad projector. -/
theorem generatedEleventh_octad_projection_actual :
    generatedEleventhOctadProjection =
      Matrix.diagonal (fun i =>
        if golayOctadWord generatedEleventhSectionOctad i = 0 then (0 : ℝ) else 1) := by
  ext i j
  simp only [generatedEleventhOctadProjection, Matrix.diagonal_apply,
    generatedEleventh_section_octad_support]
  by_cases hij : i = j
  · subst j
    cases Nat.testBit 0x22e122 i.val <;> simp
  · simp [hij]

/-- Every entire actual matrix fixer preserves the genuine E8 section after conjugation by Xi. -/
theorem generatedEleventh_matrix_fix_conjugate_E8 (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedEleventhAxis).1 =
      (griessConwayEncode generatedEleventhAxis).1) :
    co1XiIsometry * g * co1XiIsometry⁻¹ ∈
      generatedAxisE8SectionStabilizer (golayOctadWord generatedEleventhSectionOctad) := by
  rw [generatedAxisE8SectionStabilizer_mem]
  apply (generatedAxisE8_matrix_action_iff_section_stabilizer _ _).mp
  rw [← generatedEleventh_octad_projection_actual, ← generatedEleventh_section_xi_actual]
  rw [map_mul, map_mul]
  change conwayMatrixAction co1XiIsometry (conwayMatrixAction g
    (conwayMatrixAction co1XiIsometry⁻¹
      (conwayMatrixAction co1XiIsometry generatedEleventhCoordinateSection))) = _
  have hcancel : conwayMatrixAction co1XiIsometry⁻¹
      (conwayMatrixAction co1XiIsometry generatedEleventhCoordinateSection) =
        generatedEleventhCoordinateSection := by
    rw [map_inv]
    exact (conwayMatrixAction co1XiIsometry).symm_apply_apply _
  rw [hcancel, generatedEleventh_matrix_fix_section g hg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
