/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhTrianglePermutationGroup

/-! Exact physical membership in the genuine seventh triangle permutation subgroup. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The constructed subgroup is the entire actual octad-and-triangle permutation stabilizer. -/
theorem generatedSeventh_triangle_permutation_mem_iff (p : golayAutomorphismSubgroup) :
    p ∈ generatedSeventhTrianglePermutationSubgroup ↔
      golayPermute p.val (golayOctadWord generatedSeventhSectionOctad) =
        golayOctadWord generatedSeventhSectionOctad ∧
      p • generatedSeventhTriangleCoordinates = generatedSeventhTriangleCoordinates := by
  constructor
  · exact generatedSeventh_triangle_permutation_preserves p
  · rintro ⟨ho, ht⟩
    let c := generatedSeventhTriangleTransportPermutation
    let q := c⁻¹ * p * c
    have hc : golayPermute c.val (golayOctadWord generatedFifthFlagOctad) =
        golayOctadWord generatedSeventhSectionOctad :=
      generatedSeventh_triangle_transport_spec.2.2.2
    have hct : c • generatedSeventhTriangleCoordinates = generatedSeventhTriangleCoordinates :=
      generatedSeventh_triangle_transport_fixed
    have hqo : golayPermute q.val (golayOctadWord generatedFifthFlagOctad) =
        golayOctadWord generatedFifthFlagOctad := by
      change golayPermute (c.val⁻¹ * p.val * c.val)
        (golayOctadWord generatedFifthFlagOctad) = _
      rw [golayPermute_mul, golayPermute_mul, hc, ho, ← hc, golayPermute_inv]
    have hqt : q • generatedSeventhTriangleCoordinates = generatedSeventhTriangleCoordinates := by
      change (c⁻¹ * p * c) • generatedSeventhTriangleCoordinates = _
      rw [mul_smul, mul_smul, hct, ht, inv_smul_eq_iff.mpr hct.symm]
    have hqm : q ∈ generatedFifthSelectedOctadSubgroup :=
      (generatedFifthSelectedOctadSubgroup_mem q).mpr hqo
    apply Subgroup.mem_map.mpr
    refine ⟨q, Subgroup.mem_map.mpr ⟨⟨q, hqm⟩, hqt, rfl⟩, ?_⟩
    change c * q * c⁻¹ = p
    simp [q, mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
