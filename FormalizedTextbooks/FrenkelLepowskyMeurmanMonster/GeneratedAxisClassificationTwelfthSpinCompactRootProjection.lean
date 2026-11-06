/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactCompatibility
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpatialProjection

/-! Compact root-image lifts retain the exact Conway classes of all original whole matrix fixers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
-- Retain the actual central sign padding and check every complete original binary column.
private theorem root_source_binary : ∀ (g : Fin 3) (j : Fin 24),
    generatedTwelfthSectionPackedMaskWord (generatedTwelfthMatrixFixerWord g)
      (2 ^ j.val) = generatedTwelfthSpinCompactBinaryColumns ⟨g.val, by omega⟩ j := by
  decide +kernel

private theorem binary_equiv_eq_of_columns
    (e f : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (h : ∀ j : Fin 24,
      e (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        f (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val))) : e = f := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  simpa only [Pi.basisFun_apply, generatedTwelfth_spin_compact_binary_basis] using h j

/-- Every compact root lift retains the full original Conway class, including sign padding. -/
theorem generatedTwelfth_spin_compact_root_spatial_projection (g : Fin 3) :
    (QuotientGroup.mk (generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩) : Co1) =
      QuotientGroup.mk (generatedTwelfthMatrixFixer g).val := by
  apply co1BinaryAction_injective
  change leechBinaryAction (generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩) =
    leechBinaryAction (generatedTwelfthMatrixFixer g).val
  apply binary_equiv_eq_of_columns
  intro j
  have h := generatedTwelfth_section_word_packed_actual (generatedTwelfthMatrixFixerWord g)
    (2 ^ j.val)
  rw [root_source_binary] at h
  exact (generatedTwelfth_spin_compact_source_binary_actual ⟨g.val, by omega⟩ j).trans h.symm

/-- The compact genuine local root lift projects to the whole original matrix fixer's class. -/
theorem generatedTwelfth_spin_compact_root_projection (g : Fin 3) :
    projH (generatedTwelfthSpinCompactLocal ⟨g.val, by omega⟩) =
      (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val : Co1) := by
  rw [generatedTwelfth_spin_compact_projection,
    generatedTwelfth_spin_compact_root_spatial_projection]

/-- Every compact root lift fixes the entire actual matrix; central lattice signs preserve it. -/
theorem generatedTwelfth_spin_compact_root_matrix_fixing (g : Fin 3) :
    conwayMatrixAction (generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩)
        (griessConwayEncode generatedTwelfthAxis).1 =
      (griessConwayEncode generatedTwelfthAxis).1 := by
  have hk : generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩ *
      (generatedTwelfthMatrixFixer g).val⁻¹ ∈ signsSubgroup := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' signsSubgroup)
      (generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩ *
        (generatedTwelfthMatrixFixer g).val⁻¹) = 1
    rw [map_mul, map_inv]
    change (QuotientGroup.mk (generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩) : Co1) *
      (QuotientGroup.mk (generatedTwelfthMatrixFixer g).val)⁻¹ = 1
    rw [generatedTwelfth_spin_compact_root_spatial_projection, mul_inv_cancel]
  have hf : (generatedTwelfthMatrixFixer g).val ∈ generatedTwelfthSpatialStabilizer :=
    generatedTwelfth_matrix_fixer_actual_matrix g
  have he := generatedTwelfthSpatialStabilizer.mul_mem
    (generatedTwelfth_signs_le_spatial hk) hf
  have hcancel : (generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩ *
      (generatedTwelfthMatrixFixer g).val⁻¹) * (generatedTwelfthMatrixFixer g).val =
        generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩ := by group
  rw [hcancel] at he
  change conwayMatrixAction (generatedTwelfthSpinCompactSpatial ⟨g.val, by omega⟩)
    (griessConwayEncode generatedTwelfthAxis).1 = _ at he
  exact he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
