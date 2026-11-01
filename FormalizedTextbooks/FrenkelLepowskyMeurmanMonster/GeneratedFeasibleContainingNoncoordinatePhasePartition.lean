/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSelfReturnExact

/-! The complete actual mate-zero remainder of the containing rooted-section phase partition. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original containing A-vectors whose genuine preferred mate coordinate vanishes. -/
def generatedFeasibleContainingNoncoordinateAxes : Set GriessSpace :=
  {x | x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleContainingOctadDestination ∧
      (griessConwayEncode x).2.1 generatedFeasibleMateLabel = 0}

/-- Every vector in either actual coordinate phase sector has a nonzero preferred mate. -/
theorem generatedFeasibleContaining_coordinate_mate_nonzero (x : GriessSpace)
    (hx : x ∈ generatedFeasibleContainingCoordinatePhaseSectors) :
    (griessConwayEncode x).2.1 generatedFeasibleMateLabel ≠ 0 := by
  change x ∈ generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingOctadDestination ∪
    generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare at hx
  rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rw [generatedFeasibleContaining_N_mate_coordinate,
      generatedFeasibleContainingCoordinateFirst_mate]
    norm_num
  · rw [generatedFeasibleContaining_N_mate_coordinate,
      generatedFeasibleContainingCoordinateSecond_mate]
    norm_num

/-- On the entire original containing A orbit, mate zero is precisely noncoordinate section data.
-/
theorem generatedFeasibleContaining_mate_zero_iff_noncoordinate (x : GriessSpace)
    (hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) :
    (griessConwayEncode x).2.1 generatedFeasibleMateLabel = 0 ↔
      x ∉ generatedFeasibleContainingCoordinatePhaseSectors := by
  constructor
  · intro hm hc
    exact generatedFeasibleContaining_coordinate_mate_nonzero x hc hm
  · intro hc
    by_contra hm
    exact hc (generatedFeasibleContaining_mate_nonzero_coordinate ⟨x, hx⟩ hm)

/-- The actual mate-zero vectors are exactly the complement of all 77-by-128 coordinate fibers.
-/
theorem generatedFeasibleContainingNoncoordinateAxes_eq_difference :
    generatedFeasibleContainingNoncoordinateAxes =
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
        generatedFeasibleContainingOctadDestination \
          generatedFeasibleContainingCoordinatePhaseSectors := by
  ext x
  constructor
  · rintro ⟨hx, hm⟩
    exact ⟨hx, (generatedFeasibleContaining_mate_zero_iff_noncoordinate x hx).mp hm⟩
  · rintro ⟨hx, hm⟩
    exact ⟨hx, (generatedFeasibleContaining_mate_zero_iff_noncoordinate x hx).mpr hm⟩

/-- The genuine mate-zero remainder contains exactly 7,276,544 actual containing A-vectors. -/
theorem generatedFeasibleContainingNoncoordinateAxes_card :
    Nat.card generatedFeasibleContainingNoncoordinateAxes = 7276544 := by
  have : Finite (MulAction.orbit
      (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) := Nat.finite_of_card_ne_zero (by
    rw [generatedFeasibleContainingOctad_actual_A_orbit_card]
    decide)
  rw [generatedFeasibleContainingNoncoordinateAxes_eq_difference, Nat.card_coe_set_eq,
    Set.ncard_sdiff' generatedFeasibleContainingCoordinatePhaseSectors_subset_A,
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    generatedFeasibleContainingOctad_actual_A_orbit_card,
    generatedFeasibleContainingCoordinatePhaseSectors_card]

/-- The complete actual containing A orbit is covered by coordinate and mate-zero vectors. -/
theorem generatedFeasibleContaining_coordinate_noncoordinate_partition :
    generatedFeasibleContainingCoordinatePhaseSectors ∪
      generatedFeasibleContainingNoncoordinateAxes =
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingOctadDestination := by
  rw [generatedFeasibleContainingNoncoordinateAxes_eq_difference]
  ext x
  constructor
  · rintro (hc | ⟨hx, _⟩)
    · exact generatedFeasibleContainingCoordinatePhaseSectors_subset_A hc
    · exact hx
  · intro hx
    by_cases hc : x ∈ generatedFeasibleContainingCoordinatePhaseSectors
    · exact Or.inl hc
    · exact Or.inr ⟨hx, hc⟩

/-- Every genuine noncoordinate image has the exact original triality first-coefficient formula.
-/
theorem generatedFeasibleContaining_noncoordinate_triality_first (x : GriessSpace)
    (hx : x ∈ generatedFeasibleContainingNoncoordinateAxes) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      (griessConwayEncode x).1 0 1 + (1 / 2 : ℝ) := by
  rw [generatedFeasibleContaining_triality_first_coordinate,
    generatedFeasibleContaining_first_coordinate x hx.1, hx.2, sub_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
