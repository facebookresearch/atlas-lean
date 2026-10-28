/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSpatialGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignProjectionCount

/-! The exact remaining original projection-generator gates for the seventh full-axis count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual lifts of the triangle permutations and the 27 original signed spatial words suffice.
The two explicit inputs are full-axis projection memberships, not matrix-preservation claims. -/
theorem generatedSeventh_projection_eq_spatial_of_generator_lifts
    (hp : ∀ p : generatedSeventhTrianglePermutationSubgroup,
      QuotientGroup.mk' signsSubgroup (golayPermutationIsometry p.val) ∈
        generatedSeventhProjectedAxisStabilizer)
    (hw : ∀ k : Fin 27, QuotientGroup.mk' signsSubgroup (generatedSeventhFrameOrbitElement k).val ∈
      generatedSeventhProjectedAxisStabilizer) :
    generatedSeventhProjectedAxisStabilizer = generatedSeventhCo1SpatialStabilizer := by
  apply le_antisymm generatedSeventhProjectedAxisStabilizer_le_spatial
  change generatedSeventhSpatialStabilizer.map (QuotientGroup.mk' signsSubgroup) ≤ _
  apply (Subgroup.map_le_iff_le_comap).mpr
  rw [← generatedSeventhSpatialGenerated_eq]
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨v, rfl⟩ | (⟨p, rfl⟩ | ⟨k, rfl⟩))
  · exact generatedSeventhProjectedSignSubgroup_le_axis
      ⟨generatedSeventhSpatialSignHom v, ⟨v, rfl⟩, rfl⟩
  · exact hp p
  · exact hw k

/-- Those genuine generator lifts give the full original H stabilizer order. -/
theorem generatedSeventh_local_stabilizer_card_of_generator_lifts
    (hp : ∀ p : generatedSeventhTrianglePermutationSubgroup,
      QuotientGroup.mk' signsSubgroup (golayPermutationIsometry p.val) ∈
        generatedSeventhProjectedAxisStabilizer)
    (hw : ∀ k : Fin 27, QuotientGroup.mk' signsSubgroup (generatedSeventhFrameOrbitElement k).val ∈
      generatedSeventhProjectedAxisStabilizer) :
    Nat.card generatedSeventhLocalAxisStabilizer = 318504960 := by
  rw [generatedSeventh_local_stabilizer_card_range,
    generatedSeventh_projection_eq_spatial_of_generator_lifts hp hw,
    generatedSeventhCo1SpatialStabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
