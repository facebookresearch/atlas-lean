/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SectionStabilizerCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderExact

/-! Exact stabilizer of the whole actual ninth matrix. Full axis fixation is separate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All actual lattice isometries fixing the whole actual ninth matrix. -/
def generatedNinthSpatialStabilizer : Subgroup leechIsomSubgroup where
  carrier := {g | conwayMatrixAction g (griessConwayEncode generatedNinthAxis).1 =
    (griessConwayEncode generatedNinthAxis).1}
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

/-- The whole actual matrix stabilizer has order 178362777600 in Co0. -/
theorem generatedNinthSpatialStabilizer_card :
    Nat.card generatedNinthSpatialStabilizer = 178362777600 := by
  let : MulAction leechIsomSubgroup (Matrix (Fin 24) (Fin 24) ℝ) :=
    { smul := fun g A => conwayMatrixAction g A
      one_smul := by intro A; change conwayMatrixAction 1 A = A; rw [map_one]; rfl
      mul_smul := by
        intro g h A
        change conwayMatrixAction (g * h) A = conwayMatrixAction g (conwayMatrixAction h A)
        rw [map_mul]
        rfl }
  have hS : generatedNinthSpatialStabilizer =
      MulAction.stabilizer leechIsomSubgroup generatedNinthLowProjection := by
    ext g
    exact generatedNinth_matrix_stabilizer_iff g
  have hC : generatedAxisE8SectionStabilizer (golayOctadWord generatedNinthSectionOctad) =
      MulAction.stabilizer leechIsomSubgroup generatedNinthSectionProjection := by
    ext g
    change generatedAxisE8ImageSection g (golayOctadWord generatedNinthSectionOctad) =
      generatedAxisE8CoordinateSection (golayOctadWord generatedNinthSectionOctad) ↔ _
    exact (generatedAxisE8_matrix_action_iff_section_stabilizer
      (golayOctadWord generatedNinthSectionOctad) g).symm
  have hT : generatedNinthSectionProjection =
      generatedNinthSectionTransport • generatedNinthLowProjection :=
    generatedNinth_section_projection_transport.symm
  calc
    _ = Nat.card (MulAction.stabilizer leechIsomSubgroup generatedNinthLowProjection) := by
      rw [hS]
    _ = Nat.card (MulAction.stabilizer leechIsomSubgroup generatedNinthSectionProjection) :=
      Nat.card_congr (MulAction.stabilizerEquivStabilizer hT).toEquiv
    _ = Nat.card (generatedAxisE8SectionStabilizer
        (golayOctadWord generatedNinthSectionOctad)) := by rw [hC]
    _ = _ := generatedAxisE8_sectionStabilizer_card generatedNinthSectionOctad

/-- Both genuine central lattice signs fix the entire actual ninth matrix. -/
theorem generatedNinth_signs_le_spatial : signsSubgroup ≤ generatedNinthSpatialStabilizer := by
  intro g hg
  rcases hg with hg | hg
  · have he : g = 1 := Subtype.ext hg
    subst g
    exact generatedNinthSpatialStabilizer.one_mem
  · have hm : leechIsomMatrix g = -(1 : Matrix (Fin 24) (Fin 24) ℝ) := by
      ext i j
      change g.val (Pi.single j 1) i = _
      rw [hg]
      simp [Pi.single_apply, Matrix.neg_apply, Matrix.one_apply]
    change conwayMatrixAction g _ = _
    rw [conwayMatrixAction_eq_conjugate, hm, Matrix.transpose_neg, Matrix.transpose_one,
      Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

/-- The actual ninth matrix stabilizer in the genuine central-sign quotient. -/
def generatedNinthCo1SpatialStabilizer : Subgroup Co1 :=
  generatedNinthSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup)

/-- The whole actual matrix stabilizer has index 46621575 in Co0. -/
theorem generatedNinthSpatialStabilizer_index :
    generatedNinthSpatialStabilizer.index = 46621575 := by
  have h := generatedNinthSpatialStabilizer.card_mul_index
  rw [generatedNinthSpatialStabilizer_card, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 178362777600)
    (h.trans (by decide : 8315553613086720000 = 178362777600 * 46621575))

/-- Central signs preserve the index in the actual Co1 quotient. -/
theorem generatedNinthCo1SpatialStabilizer_index :
    generatedNinthCo1SpatialStabilizer.index = 46621575 := by
  change (generatedNinthSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedNinthSpatialStabilizer_index
  · rw [QuotientGroup.ker_mk']
    exact generatedNinth_signs_le_spatial

/-- The whole actual ninth matrix stabilizer has order 89181388800 in Co1. -/
theorem generatedNinthCo1SpatialStabilizer_card :
    Nat.card generatedNinthCo1SpatialStabilizer = 89181388800 := by
  have h := generatedNinthCo1SpatialStabilizer.card_mul_index
  rw [generatedNinthCo1SpatialStabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 46621575)
    (h.trans (by decide : 4157776806543360000 = 89181388800 * 46621575))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
