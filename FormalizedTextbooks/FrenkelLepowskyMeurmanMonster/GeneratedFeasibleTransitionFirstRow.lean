/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionReciprocity

/-! The actual secondary feasible orbit has exactly one transition coset to the singleton orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original singleton-to-secondary feasible transition is counted on genuine cosets. -/
theorem generatedFeasibleActualTransition_first_secondary_card (p : Fin 276) :
    Nat.card (generatedFeasibleActualTransitionCosets p
      (conwayShortAxis (Sum.inl (0, p)) 1) (generatedFeasibleSecondaryAxis p)) = 93150 :=
  generatedFeasibleTransitionDestination_first_fiber_card p

/-- The actual restricted orbit of the opposite pair axis has one vector. -/
theorem generatedFeasibleActualOrbit_first_card (p : Fin 276) :
    Nat.card (MulAction.orbit (localAxisStabilizer p)
      (conwayShortAxis (Sum.inl (0, p)) 1)) = 1 := by
  change Nat.card (generatedFeasibleLocalAnchorOrbit p) = 1
  exact generatedFeasibleLocalAnchorOrbit_card p

/-- Exactly one genuine transition coset from the secondary orbit returns to the singleton orbit. -/
theorem generatedFeasibleActualTransition_secondary_first_card (p : Fin 276) :
    Nat.card (generatedFeasibleActualTransitionCosets p (generatedFeasibleSecondaryAxis p)
      (conwayShortAxis (Sum.inl (0, p)) 1)) = 1 := by
  have h := generatedFeasibleActualTransition_reciprocity p
    (conwayShortAxis (Sum.inl (0, p)) 1) (generatedFeasibleSecondaryAxis p)
  have hsecondary : Nat.card (MulAction.orbit (localAxisStabilizer p)
      (generatedFeasibleSecondaryAxis p)) = 93150 :=
    generatedFeasibleSecondaryLocalOrbit_card p
  rw [generatedFeasibleActualOrbit_first_card,
    generatedFeasibleActualTransition_first_secondary_card, hsecondary, one_mul] at h
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 93150)
  exact h.symm.trans (Nat.mul_one 93150).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
