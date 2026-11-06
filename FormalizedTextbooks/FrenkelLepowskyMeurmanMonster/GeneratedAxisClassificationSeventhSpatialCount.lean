/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2TriangleFlag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatialStabilizer

/-! Exact actual spatial matrix stabilizers of the seventh representative. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original matrix stabilizer is precisely the genuine section and intrinsic A2-plane flag. -/
theorem generatedSeventhSpatialStabilizer_eq_flag :
    generatedSeventhSpatialStabilizer = MulAction.stabilizer leechIsomSubgroup
      (generatedAxisE8CoordinateSection (golayOctadWord generatedSeventhSectionOctad),
        leechSeventhE8A2Plane 537) := by
  ext g
  change conwayMatrixAction g (griessConwayEncode generatedSeventhAxis).1 =
    (griessConwayEncode generatedSeventhAxis).1 ↔ _
  rw [generatedSeventh_axis_matrix_section_plane_fixed_iff,
    leechSeventhTriangle_projection_fixed_iff]
  change _ ↔ g • (generatedAxisE8CoordinateSection
    (golayOctadWord generatedSeventhSectionOctad), leechSeventhE8A2Plane 537) = _
  rw [Prod.ext_iff]
  rfl

/-- The whole actual seventh matrix stabilizer in Co0 has exactly 159252480 elements. -/
theorem generatedSeventhSpatialStabilizer_card :
    Nat.card generatedSeventhSpatialStabilizer = 159252480 := by
  rw [generatedSeventhSpatialStabilizer_eq_flag]
  exact leechSeventhA2Flag_coordinate_stabilizer_card generatedSeventhSectionOctad
    (leechSeventhE8A2Plane 537) leechSeventhTriangle_intrinsic

/-- Both actual central lattice signs fix the original seventh matrix. -/
theorem generatedSeventh_signs_le_spatial : signsSubgroup ≤ generatedSeventhSpatialStabilizer := by
  intro g hg
  rcases hg with hg | hg
  · have he : g = 1 := Subtype.ext hg
    subst g
    exact generatedSeventhSpatialStabilizer.one_mem
  · have hm : leechIsomMatrix g = -(1 : Matrix (Fin 24) (Fin 24) ℝ) := by
      ext i j
      change g.val (Pi.single j 1) i = _
      rw [hg]
      simp [Pi.single_apply, Matrix.neg_apply, Matrix.one_apply]
    change conwayMatrixAction g _ = _
    rw [conwayMatrixAction_eq_conjugate, hm, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one, neg_neg]

/-- The original seventh matrix stabilizer has its actual index in full Co0. -/
theorem generatedSeventhSpatialStabilizer_index :
    generatedSeventhSpatialStabilizer.index = 52216164000 := by
  have h := generatedSeventhSpatialStabilizer.card_mul_index
  rw [generatedSeventhSpatialStabilizer_card, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 159252480)
    (h.trans (by decide : 8315553613086720000 = 159252480 * 52216164000))

/-- Quotienting actual central signs preserves the whole matrix stabilizer index. -/
theorem generatedSeventhCo1SpatialStabilizer_index :
    generatedSeventhCo1SpatialStabilizer.index = 52216164000 := by
  change (generatedSeventhSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedSeventhSpatialStabilizer_index
  · rw [QuotientGroup.ker_mk']
    exact generatedSeventh_signs_le_spatial

/-- The whole actual seventh matrix stabilizer in Co1 has exactly 79626240 elements. -/
theorem generatedSeventhCo1SpatialStabilizer_card :
    Nat.card generatedSeventhCo1SpatialStabilizer = 79626240 := by
  have h := generatedSeventhCo1SpatialStabilizer.card_mul_index
  rw [generatedSeventhCo1SpatialStabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 52216164000)
    (h.trans (by decide : 4157776806543360000 = 79626240 * 52216164000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
