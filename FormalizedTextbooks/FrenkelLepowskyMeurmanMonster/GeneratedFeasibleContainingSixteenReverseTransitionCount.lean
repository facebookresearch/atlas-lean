/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenOrbitCount

/-! Actual weighted reciprocity closes the reverse odd-to-containing input count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Exactly42 complete original odd-class input cosets return to the containing class. -/
theorem generatedFeasibleActualTransition_odd_containing_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleSecondaryOddDestination generatedFeasibleContainingOctadDestination) = 42 := by
  have h := generatedFeasibleActualTransition_reciprocity generatedFeasiblePhysicalRootPair
    generatedFeasibleContainingOctadDestination generatedFeasibleSecondaryOddDestination
  rw [generatedFeasibleContainingOctad_actual_A_orbit_card,
    generatedFeasibleActualTransition_containing_odd_card,
    generatedFeasibleOddDestination_actual_A_orbit_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
