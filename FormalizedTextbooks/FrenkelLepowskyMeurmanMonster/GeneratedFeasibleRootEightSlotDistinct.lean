/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleRootEightSlotOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleFifthSlotOrbitCount
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSeventhSlotOrbitCount

/-! The slot-9 feasible A orbit (source label 10A1 of Höhn–Seysen, arXiv:2508.01037, Table 3)
differs from the nine closed feasible A orbits. Distinct proved actual orbit sizes suffice;
no source class label is used. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A vector whose actual A orbit has a different size cannot share the prototype's orbit. -/
theorem generatedFeasibleRootEightSlot_not_mem_of_card_ne {z : GriessSpace}
    (hz : Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) z) ≠
      4000762036224) :
    generatedFeasibleRootEightSlotPrototype ∉
      MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair) z := by
  intro hx
  apply hz
  rw [← MulAction.orbit_eq_iff.mpr hx]
  exact generatedFeasibleRootEightSlot_actual_A_orbit_card

/-- The prototype lies in none of the nine closed feasible A orbits, listed in Table 3 order:
the opposite axis, the secondary axis, the containing-octad, outside-octad and odd
destinations, the one-eighth destination, and the slot-6, slot-7 and slot-8 prototypes. -/
theorem generatedFeasibleRootEightSlot_not_mem_closed :
    generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) ∧
      generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) ∧
      generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingOctadDestination ∧
      generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleOutsideOctadDestination ∧
      generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleSecondaryOddDestination ∧
      generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleContainingNewDestination ∧
      generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleFifthSlotPrototype ∧
      generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleSixthSlotPrototype ∧
      generatedFeasibleRootEightSlotPrototype ∉
        MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
          generatedFeasibleSeventhSlotPrototype := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply generatedFeasibleRootEightSlot_not_mem_of_card_ne
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
  · rw [generatedFeasibleFifthSlot_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleSixthSlot_actual_A_orbit_card]
    decide
  · rw [generatedFeasibleSeventhSlot_actual_A_orbit_card]
    decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
