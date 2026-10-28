/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionFirstRow
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOutsideOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOddDestinationOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthActualOrbitCount

/-! The slot-7 feasible A orbit differs from the six closed feasible A orbits.
Distinct proved actual orbit sizes suffice; no source class label is used. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A vector whose actual A orbit has a different size cannot share the prototype's orbit. -/
theorem generatedFeasibleSixthSlot_not_mem_of_card_ne {z : GriessSpace}
    (hz : Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) z) ≠
      9646899200) :
    generatedFeasibleSixthSlotPrototype ∉
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) z := by
  intro hx
  apply hz
  rw [← MulAction.orbit_eq_iff.mpr hx]
  exact generatedFeasibleSixthSlot_actual_A_orbit_card

/-- The prototype lies in none of the six closed feasible A orbits, listed in Table 3 order:
the opposite axis, the secondary axis, the containing-octad, outside-octad and odd
destinations, and the one-eighth destination. -/
theorem generatedFeasibleSixthSlot_not_mem_closed :
    generatedFeasibleSixthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) ∧
      generatedFeasibleSixthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) ∧
      generatedFeasibleSixthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingOctadDestination ∧
      generatedFeasibleSixthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleOutsideOctadDestination ∧
      generatedFeasibleSixthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleSecondaryOddDestination ∧
      generatedFeasibleSixthSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingNewDestination := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply generatedFeasibleSixthSlot_not_mem_of_card_ne
  · rw [generatedFeasibleActualOrbit_first_card]
    decide
  · change Nat.card (generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair) ≠ _
    rw [generatedFeasibleSecondaryLocalOrbit_card]
    decide
  · rw [generatedFeasibleContainingOctad_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleOutsideOctad_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleOddDestination_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleContainingEighth_actual_A_orbit_card]
    decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
