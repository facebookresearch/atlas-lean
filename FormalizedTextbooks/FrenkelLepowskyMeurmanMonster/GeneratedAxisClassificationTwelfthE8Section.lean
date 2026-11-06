/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpatialSection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SectionStabilizerCount

/-! The actual matrix stabilizer preserves a genuine original integral coordinate E8 section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine original Golay octad with source code label 2052. -/
def generatedTwelfthSectionOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm ⟨2052, by decide +kernel⟩

/-- The source catalogue address retains exactly its original Golay code label. -/
theorem generatedTwelfth_section_octad_label :
    golayOctadLabel generatedTwelfthSectionOctad = 2052 :=
  congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨2052, by decide +kernel⟩)

/-- The genuine octad has exactly the eight physical positions recovered from the actual matrix. -/
theorem generatedTwelfth_section_octad_support (i : Fin 24) :
    golayOctadWord generatedTwelfthSectionOctad i = 0 ↔
      Nat.testBit 0x0f000f i.val = false := by
  rw [golayOctadWord, generatedTwelfth_section_octad_label, golayLabelEncoder_boolean]
  fin_cases i <;> decide +kernel

/-- The polynomial projector is the real projection onto the actual integral coordinate section. -/
theorem generatedTwelfth_coordinate_section_actual :
    generatedTwelfthCoordinateSection =
      Matrix.diagonal (fun i =>
        if golayOctadWord generatedTwelfthSectionOctad i = 0 then (0 : ℝ) else 1) := by
  ext i j
  simp only [generatedTwelfthCoordinateSection, generatedTwelfthSectionInteger,
    Matrix.map_apply, Matrix.diagonal_apply, generatedTwelfth_section_octad_support]
  by_cases hij : i = j
  · subst j
    cases Nat.testBit 0x0f000f i.val <;> simp
  · simp [hij]

/-- The entire genuine spatial matrix stabilizer preserves this actual integral E8 section. -/
theorem generatedTwelfth_matrix_fix_E8_section (g : leechIsomSubgroup)
    (hg : conwayMatrixAction g (griessConwayEncode generatedTwelfthAxis).1 =
      (griessConwayEncode generatedTwelfthAxis).1) :
    g ∈ generatedAxisE8SectionStabilizer (golayOctadWord generatedTwelfthSectionOctad) := by
  rw [generatedAxisE8SectionStabilizer_mem]
  apply (generatedAxisE8_matrix_action_iff_section_stabilizer _ g).mp
  have h := generatedTwelfth_matrix_fix_section g hg
  rwa [generatedTwelfth_coordinate_section_actual] at h

/-- The actual full section stabilizer has its previously proved unconditional Co0 order. -/
theorem generatedTwelfth_E8_section_stabilizer_card :
    Nat.card (generatedAxisE8SectionStabilizer (golayOctadWord generatedTwelfthSectionOctad)) =
      178362777600 :=
  generatedAxisE8_sectionStabilizer_card generatedTwelfthSectionOctad


/-- Genuine lattice isometries fixing the entire original actual matrix. -/
def generatedTwelfthSpatialStabilizer : Subgroup leechIsomSubgroup where
  carrier := {g | conwayMatrixAction g (griessConwayEncode generatedTwelfthAxis).1 =
    (griessConwayEncode generatedTwelfthAxis).1}
  one_mem' := by
    change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  mul_mem' := by
    intro g h hg hh
    change conwayMatrixAction (g * h) _ = _
    rw [map_mul]
    change conwayMatrixAction g (conwayMatrixAction h _) = _
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change conwayMatrixAction g⁻¹ _ = _
    rw [map_inv]
    change (conwayMatrixAction g).symm _ = _
    exact (conwayMatrixAction g).symm_apply_eq.mpr hg.symm

/-- The whole actual matrix stabilizer lies in the genuine original E8 section stabilizer. -/
theorem generatedTwelfth_spatial_le_E8_section :
    generatedTwelfthSpatialStabilizer ≤
      generatedAxisE8SectionStabilizer (golayOctadWord generatedTwelfthSectionOctad) := by
  intro g hg
  exact generatedTwelfth_matrix_fix_E8_section g hg

/-- The original matrix stabilizer has an unconditional actual Co0 order upper bound. -/
theorem generatedTwelfth_spatial_card_upper :
    Nat.card generatedTwelfthSpatialStabilizer ≤ 178362777600 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have h := Subgroup.card_le_of_le generatedTwelfth_spatial_le_E8_section
  rwa [generatedTwelfth_E8_section_stabilizer_card] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
