/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMatrixRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SectionStabilizerCount

/-! The actual two seventh-axis supports combine to a genuine coordinate E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine Golay octad with original MOG coordinates twelve through nineteen. -/
def generatedSeventhSectionOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm ⟨6, by decide +kernel⟩

/-- This actual catalogue address has the literal source code label six. -/
theorem generatedSeventh_section_octad_label : golayOctadLabel generatedSeventhSectionOctad = 6 :=
  congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨6, by decide +kernel⟩)

/-- The original octad's binary support is exactly the eight stated physical coordinates. -/
theorem generatedSeventh_section_octad_support (i : Fin 24) :
    golayOctadWord generatedSeventhSectionOctad i ≠ 0 ↔ 12 ≤ i.val ∧ i.val < 20 := by
  rw [golayOctadWord, generatedSeventh_section_octad_label, golayLabelEncoder_boolean]
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 2000000 in
-- Normalize all 576 entries of the original real coordinate projection.
/-- The two spatial supports sum to three times the genuine E8 coordinate projection. -/
theorem generatedSeventh_support_sum_section :
    generatedSeventhPlaneSupport + generatedSeventhSixSupport = (3 : ℝ) •
      Matrix.diagonal (fun i =>
        if golayOctadWord generatedSeventhSectionOctad i = 0 then (0 : ℝ) else 1) := by
  ext i j
  change (generatedSeventhPlaneNumerator i j : ℝ) +
    (generatedSeventhSixNumerator i j : ℝ) =
      3 * (Matrix.diagonal (fun i =>
        if golayOctadWord generatedSeventhSectionOctad i = 0 then (0 : ℝ) else 1)) i j
  simp only [Matrix.diagonal_apply]
  have hi := generatedSeventh_section_octad_support i
  have hz : golayOctadWord generatedSeventhSectionOctad i = 0 ↔
      ¬ (12 ≤ i.val ∧ i.val < 20) := by tauto
  simp only [hz]
  fin_cases i <;> fin_cases j <;>
    norm_num [generatedSeventhPlaneNumerator, generatedSeventhSixNumerator,
      generatedSeventhFive, generatedSeventhTriangle]

/-- The actual seventh matrix fixes precisely its genuine E8 section and two-root support. -/
theorem generatedSeventh_axis_matrix_section_plane_fixed_iff (g : leechIsomSubgroup) :
    conwayMatrixAction g (griessConwayEncode generatedSeventhAxis).1 =
        (griessConwayEncode generatedSeventhAxis).1 ↔
      g ∈ generatedAxisE8SectionStabilizer (golayOctadWord generatedSeventhSectionOctad) ∧
        conwayMatrixAction g generatedSeventhPlaneSupport = generatedSeventhPlaneSupport := by
  rw [generatedSeventh_axis_matrix_support_fixed_iff]
  have he := generatedAxisE8_matrix_action_iff_section_stabilizer
    (golayOctadWord generatedSeventhSectionOctad) g
  rw [← generatedAxisE8SectionStabilizer_mem] at he
  constructor
  · rintro ⟨hp, hs⟩
    refine ⟨he.mp ?_, hp⟩
    have h := congrArg (conwayMatrixAction g) generatedSeventh_support_sum_section
    rw [map_add, hp, hs, map_smul, generatedSeventh_support_sum_section] at h
    exact (smul_right_injective _ (by norm_num : (3 : ℝ) ≠ 0)) h.symm
  · rintro ⟨heS, hp⟩
    refine ⟨hp, ?_⟩
    have h := congrArg (conwayMatrixAction g) generatedSeventh_support_sum_section
    rw [map_add, hp, map_smul, he.mpr heS, ← generatedSeventh_support_sum_section] at h
    exact add_left_cancel h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
