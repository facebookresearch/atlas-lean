/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryPairReturnVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionActualFibers

/-! The actual secondary-to-secondary feasible transition entry is 925. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exactly 925 actual secondary-orbit vectors return to the actual secondary orbit. -/
theorem generatedFeasibleActualTransition_secondary_secondary_vectors_card :
    Nat.card (generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 925 := by
  change Nat.card {x : GriessSpace |
    x ∈ generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair ∧
      sExtra x ∈ generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair} = 925
  rw [generatedFeasibleSecondaryLocalOrbit_eq_physical,
    generatedFeasibleSecondaryReturn_eq_pair_axes, generatedFeasibleSecondaryPairReturnAxes_card]

/-- The genuine secondary-to-secondary transition coset fiber has exactly 925 elements. -/
theorem generatedFeasibleActualTransition_secondary_secondary_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 925 := by
  have h := generatedFeasibleActualTransition_fiber_balance generatedFeasiblePhysicalRootPair
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
  rw [generatedFeasibleActualTransition_secondary_secondary_vectors_card,
    generatedFeasibleSecondaryAxis_stabilizer] at h
  have hn : 0 < Nat.card (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair) := by
    rw [Nat.card_congr (localFeasibleTransitionEquiv generatedFeasiblePhysicalRootPair).toEquiv,
      localOmegaAxisIntersection_card]
    decide
  exact Nat.eq_of_mul_eq_mul_right hn h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
