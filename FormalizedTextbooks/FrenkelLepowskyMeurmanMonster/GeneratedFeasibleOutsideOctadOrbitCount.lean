/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOutsideOctadStabilizerKernel

/-! Exact actual outside-octad feasible A orbit and its genuine reverse transition count. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual whole-axis outside stabilizer has genuine index262310400 in the original A. -/
theorem generatedFeasibleOutsideOctadStabilizer_index :
    generatedFeasibleOutsideOctadStabilizer.index = 262310400 := by
  have h := generatedFeasibleOutsideOctadStabilizer.card_mul_index
  rw [generatedFeasibleOutsideOctadStabilizer_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  omega

/-- Exactly262310400 original vectors form the genuine outside-octad feasible A orbit. -/
theorem generatedFeasibleOutsideOctad_actual_A_orbit_card :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleOutsideOctadDestination) = 262310400 := by
  have h := generatedFeasibleOutsideOctadStabilizer_index
  rw [generatedFeasibleOutsideOctadStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at h
  exact h

/-- Exactly15 genuine transitions from the outside-octad A orbit return to secondary. -/
theorem generatedFeasibleActualTransition_outside_secondary_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      generatedFeasibleOutsideOctadDestination
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 15 := by
  have h := generatedFeasibleActualTransition_outside_secondary_equation
  rw [generatedFeasibleOutsideOctad_actual_A_orbit_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
