/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SectionStabilizerCount

/-! The genuine section stabilizer after quotienting the two central lattice signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both actual central lattice signs preserve every coordinate section. -/
theorem generatedAxisE8_signs_le_section_stabilizer (c : Fin 24 → ZMod 2) :
    signsSubgroup ≤ generatedAxisE8SectionStabilizer c := by
  intro g hg
  rw [generatedAxisE8SectionStabilizer_mem]
  apply generatedAxisE8_preserving_image c g
  apply generatedAxisE8_preserves_of_matrix_action c g
  rcases hg with hg | hg
  · have he : g = 1 := Subtype.ext hg
    rw [he, map_one]
    rfl
  · have hm : leechIsomMatrix g = -(1 : Matrix (Fin 24) (Fin 24) ℝ) := by
      ext i j
      simp [leechIsomMatrix, hg, Matrix.one_apply, Pi.single_apply]
    rw [conwayMatrixAction_eq_conjugate, hm]
    simp

/-- The actual section stabilizer in Co1 is the image of its actual Co0 stabilizer. -/
def generatedAxisE8Co1SectionStabilizer (c : Fin 24 → ZMod 2) : Subgroup Co1 :=
  (generatedAxisE8SectionStabilizer c).map (QuotientGroup.mk' signsSubgroup)

/-- The actual coordinate section stabilizer has index 46621575 in Co0. -/
theorem generatedAxisE8_sectionStabilizer_index (o : Fin 759) :
    (generatedAxisE8SectionStabilizer (golayOctadWord o)).index = 46621575 := by
  have h := (generatedAxisE8SectionStabilizer (golayOctadWord o)).card_mul_index
  rw [generatedAxisE8_sectionStabilizer_card, co0_card_exact] at h
  omega

/-- Quotienting the actual central signs preserves the actual section stabilizer index. -/
theorem generatedAxisE8_co1SectionStabilizer_index (o : Fin 759) :
    (generatedAxisE8Co1SectionStabilizer (golayOctadWord o)).index = 46621575 := by
  change ((generatedAxisE8SectionStabilizer (golayOctadWord o)).map
    (QuotientGroup.mk' signsSubgroup)).index = _
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective signsSubgroup)]
  · exact generatedAxisE8_sectionStabilizer_index o
  · rw [QuotientGroup.ker_mk']
    exact generatedAxisE8_signs_le_section_stabilizer _

/-- The actual Co1 section stabilizer has precisely 89181388800 elements. -/
theorem generatedAxisE8_co1SectionStabilizer_card (o : Fin 759) :
    Nat.card (generatedAxisE8Co1SectionStabilizer (golayOctadWord o)) = 89181388800 := by
  have h := (generatedAxisE8Co1SectionStabilizer (golayOctadWord o)).card_mul_index
  rw [generatedAxisE8_co1SectionStabilizer_index, co1_card_exact] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
