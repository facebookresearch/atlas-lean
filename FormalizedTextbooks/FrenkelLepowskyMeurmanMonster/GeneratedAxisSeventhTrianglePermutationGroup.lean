/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSelectedTripleOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhOctadTripleTransport

/-! The actual 5760 triangle-compatible permutations in the original seventh section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The genuine selected-octad triangle stabilizer, embedded in the actual Mathieu group. -/
def generatedSeventhSelectedTrianglePermutationSubgroup : Subgroup golayAutomorphismSubgroup :=
  (MulAction.stabilizer generatedFifthSelectedOctadSubgroup
    ({16, 17, 19} : Finset (Fin 24))).map generatedFifthSelectedOctadSubgroup.subtype

/-- Embedding the actual triangle subgroup preserves its exact cardinality. -/
theorem generatedSeventh_selected_triangle_permutation_card :
    Nat.card generatedSeventhSelectedTrianglePermutationSubgroup = 5760 := by
  rw [generatedSeventhSelectedTrianglePermutationSubgroup,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ generatedFifthSelectedOctadSubgroup.subtype
      Subtype.val_injective).toEquiv]
  exact generatedSeventh_selected_triple_stabilizer_card

/-- Actual selected-to-seventh octad transport fixing the triangle. -/
def generatedSeventhTriangleTransportPermutation : golayAutomorphismSubgroup :=
  Classical.choose leechSeventh_octad_triangle_transport

/-- The actual coordinate transport retains all three literal distinguished coordinates. -/
theorem generatedSeventh_triangle_transport_spec :
    generatedSeventhTriangleTransportPermutation.val 16 = 16 ∧
      generatedSeventhTriangleTransportPermutation.val 17 = 17 ∧
      generatedSeventhTriangleTransportPermutation.val 19 = 19 ∧
      golayPermute generatedSeventhTriangleTransportPermutation.val
        (golayOctadWord generatedFifthFlagOctad) = golayOctadWord generatedSeventhSectionOctad :=
  Classical.choose_spec leechSeventh_octad_triangle_transport

/-- The actual transport fixes the entire literal triangle set. -/
theorem generatedSeventh_triangle_transport_fixed :
    generatedSeventhTriangleTransportPermutation • generatedSeventhTriangleCoordinates =
      generatedSeventhTriangleCoordinates := by
  rw [generatedSeventhTriangleCoordinates, Finset.smul_finset_def,
    Finset.image_insert, Finset.image_insert, Finset.image_singleton]
  change ({generatedSeventhTriangleTransportPermutation.val 16,
    generatedSeventhTriangleTransportPermutation.val 17,
    generatedSeventhTriangleTransportPermutation.val 19} : Finset (Fin 24)) = _
  rw [generatedSeventh_triangle_transport_spec.1, generatedSeventh_triangle_transport_spec.2.1,
    generatedSeventh_triangle_transport_spec.2.2.1]

/-- The actual conjugated Mathieu subgroup preserving the seventh section and triangle. -/
def generatedSeventhTrianglePermutationSubgroup : Subgroup golayAutomorphismSubgroup :=
  generatedSeventhSelectedTrianglePermutationSubgroup.map
    (MulAut.conj generatedSeventhTriangleTransportPermutation).toMonoidHom

/-- Genuine conjugation preserves the original 5760-element triangle permutation count. -/
theorem generatedSeventh_triangle_permutation_card :
    Nat.card generatedSeventhTrianglePermutationSubgroup = 5760 := by
  rw [generatedSeventhTrianglePermutationSubgroup,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _
      (MulAut.conj generatedSeventhTriangleTransportPermutation).toMonoidHom
      (MulAut.conj generatedSeventhTriangleTransportPermutation).injective).toEquiv]
  exact generatedSeventh_selected_triangle_permutation_card

/-- Every actual subgroup element preserves the seventh Golay octad and literal triangle. -/
theorem generatedSeventh_triangle_permutation_preserves (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) :
    golayPermute p.val (golayOctadWord generatedSeventhSectionOctad) =
      golayOctadWord generatedSeventhSectionOctad ∧
      p • generatedSeventhTriangleCoordinates = generatedSeventhTriangleCoordinates := by
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hq
  have hsel := (generatedFifthSelectedOctadSubgroup_mem r.val).mp r.property
  have htri : r.val • generatedSeventhTriangleCoordinates =
      generatedSeventhTriangleCoordinates := hr
  let c := generatedSeventhTriangleTransportPermutation
  have hc : golayPermute c.val (golayOctadWord generatedFifthFlagOctad) =
      golayOctadWord generatedSeventhSectionOctad :=
    generatedSeventh_triangle_transport_spec.2.2.2
  have hct : c • generatedSeventhTriangleCoordinates = generatedSeventhTriangleCoordinates :=
    generatedSeventh_triangle_transport_fixed
  constructor
  · change golayPermute (c.val * r.val.val * c.val⁻¹)
      (golayOctadWord generatedSeventhSectionOctad) = _
    rw [← hc, golayPermute_mul, golayPermute_mul, golayPermute_inv, hsel]
  · change (c * r.val * c⁻¹) • generatedSeventhTriangleCoordinates = _
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hct.symm, htri, hct]

/-- The constructed genuine permutations all preserve the whole actual seventh matrix. -/
theorem generatedSeventh_triangle_permutation_spatial (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) :
    golayPermutationIsometry p ∈ generatedSeventhSpatialStabilizer := by
  obtain ⟨ho, ht⟩ := generatedSeventh_triangle_permutation_preserves p hp
  change conwayMatrixAction _ (griessConwayEncode generatedSeventhAxis).1 = _
  rw [generatedSeventh_axis_matrix_section_plane_fixed_iff]
  refine ⟨?_, generatedSeventh_permutation_plane_fixed p ht⟩
  rw [generatedAxisE8SectionStabilizer_mem]
  exact leechSeventh_coordinate_section_permutation _ _ p ho

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
