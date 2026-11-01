/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhSectionXi

/-! A genuine injective spatial stabilizer map into the original integral E8 section group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Genuine lattice isometries fixing the entire original actual matrix. -/
def generatedEleventhSpatialStabilizer : Subgroup leechIsomSubgroup where
  carrier := {g | conwayMatrixAction g (griessConwayEncode generatedEleventhAxis).1 =
    (griessConwayEncode generatedEleventhAxis).1}
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

/-- Genuine Xi embeds the complete actual matrix stabilizer into the E8 section group. -/
def generatedEleventhSpatialE8Embedding : generatedEleventhSpatialStabilizer →*
    generatedAxisE8SectionStabilizer (golayOctadWord generatedEleventhSectionOctad) where
  toFun g := ⟨co1XiIsometry * g.val * co1XiIsometry⁻¹,
    generatedEleventh_matrix_fix_conjugate_E8 g.val g.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; simp [mul_assoc]

/-- Conjugation retains every entire actual matrix fixer distinctly. -/
theorem generatedEleventh_spatial_E8_injective :
    Function.Injective generatedEleventhSpatialE8Embedding := by
  intro g h hh
  apply Subtype.ext
  have he := congrArg Subtype.val hh
  change co1XiIsometry * g.val * co1XiIsometry⁻¹ =
    co1XiIsometry * h.val * co1XiIsometry⁻¹ at he
  exact mul_left_cancel (mul_right_cancel he)

/-- The entire original spatial matrix stabilizer has an unconditional genuine E8 order bound. -/
theorem generatedEleventh_spatial_card_upper :
    Nat.card generatedEleventhSpatialStabilizer ≤ 178362777600 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have h := Nat.card_le_card_of_injective generatedEleventhSpatialE8Embedding
    generatedEleventh_spatial_E8_injective
  rwa [generatedAxisE8_sectionStabilizer_card generatedEleventhSectionOctad] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
