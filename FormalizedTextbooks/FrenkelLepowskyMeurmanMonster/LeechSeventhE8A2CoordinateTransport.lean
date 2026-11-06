/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Transport

/-! Genuine Golay permutations transport complete intrinsic A2-plane carriers
between coordinate sections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A genuine Golay permutation sends the entire actual coordinate section to its target section. -/
theorem leechSeventh_coordinate_section_permutation (c d : Fin 24 → ZMod 2)
    (p : golayAutomorphismSubgroup) (hp : golayPermute p.val c = d) :
    (generatedAxisE8CoordinateSection c).map
      (leechIntegralAction (golayPermutationIsometry p)).toLinearMap =
        generatedAxisE8CoordinateSection d := by
  ext u
  rw [Submodule.mem_map_equiv]
  change generatedOctadSupported c
      ((leechIntegralAction (golayPermutationIsometry p)).symm u).val ↔
    generatedOctadSupported d u.val
  have h := generatedOctadSupported_permutation c d p hp
    ((leechIntegralAction (golayPermutationIsometry p)).symm u)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Every actual coordinate octad section is a genuine spatial image of the selected section. -/
theorem leechSeventh_coordinate_section_reachable (o : Fin 759) :
    ∃ g : leechIsomSubgroup,
      generatedAxisE8ImageSection g (golayOctadWord generatedFifthFlagOctad) =
        generatedAxisE8CoordinateSection (golayOctadWord o) := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard (golayOctadWord generatedFifthFlagOctad)
    (golayOctadWord_mem_code _) (golayOctadWord_weight _)
  obtain ⟨q, hq⟩ := golayOctad_to_standard (golayOctadWord o)
    (golayOctadWord_mem_code _) (golayOctadWord_weight _)
  let P := golayPermutationIsometry p
  let Q := golayPermutationIsometry q
  have hP := leechSeventh_coordinate_section_permutation _ _ p hp
  have hQ := leechSeventh_coordinate_section_permutation _ _ q hq
  refine ⟨Q⁻¹ * P, ?_⟩
  change (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)).map
    (leechIntegralAction (Q⁻¹ * P)).toLinearMap = _
  rw [map_mul]
  change (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)).map
    ((leechIntegralAction Q).symm.toLinearMap.comp (leechIntegralAction P).toLinearMap) = _
  rw [Submodule.map_comp, hP]
  exact (Submodule.map_symm_eq_iff (leechIntegralAction Q)).mpr hQ

/-- Every genuine coordinate E8 section has exactly 1120 intrinsic actual A2 planes. -/
theorem leechSeventhA2PlanesIn_coordinate_card (o : Fin 759) :
    Nat.card (leechSeventhA2PlanesIn
      (generatedAxisE8CoordinateSection (golayOctadWord o))) = 1120 := by
  obtain ⟨g, hg⟩ := leechSeventh_coordinate_section_reachable o
  rw [← hg]
  exact leechSeventhA2PlanesIn_image_card g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
