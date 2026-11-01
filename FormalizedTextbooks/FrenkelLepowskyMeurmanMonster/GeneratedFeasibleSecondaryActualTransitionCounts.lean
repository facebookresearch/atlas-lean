/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryActualTransitionFibers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionReciprocity

/-! Exact genuine secondary transition entries and actual reciprocal orbit equations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exactly 4,928 original secondary vectors reach the containing-octad A class. -/
theorem generatedFeasibleActualTransition_secondary_containing_vectors_card :
    Nat.card (generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) = 4928 := by
  rw [generatedFeasibleSecondary_containing_transition_vectors]
  exact generatedFeasibleContainingOctadAxes_card

/-- Exactly 42,240 original secondary vectors reach the outside-octad A class. -/
theorem generatedFeasibleActualTransition_secondary_outside_vectors_card :
    Nat.card (generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleOutsideOctadDestination) = 42240 := by
  rw [generatedFeasibleSecondary_outside_transition_vectors]
  exact generatedFeasibleOutsideOctadAxes_card

/-- Exactly 45,056 original secondary vectors reach the odd A class. -/
theorem generatedFeasibleActualTransition_secondary_odd_vectors_card :
    Nat.card (generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleSecondaryOddDestination) = 45056 := by
  rw [generatedFeasibleSecondary_odd_transition_vectors]
  exact generatedFeasibleSecondaryOddAxes_card

/-- For this actual secondary source, vector and genuine transition-coset fibers have equal size. -/
theorem generatedFeasibleActualTransition_secondary_cosets_eq_vectors (b : GriessSpace) :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) b) =
      Nat.card (generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) b) := by
  have h := generatedFeasibleActualTransition_fiber_balance generatedFeasiblePhysicalRootPair
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) b
  rw [generatedFeasibleSecondaryAxis_stabilizer] at h
  have hn : 0 < Nat.card (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair) := by
    rw [Nat.card_congr (localFeasibleTransitionEquiv generatedFeasiblePhysicalRootPair).toEquiv,
      localOmegaAxisIntersection_card]
    decide
  exact Nat.eq_of_mul_eq_mul_right hn h

/-- Exactly 4,928 genuine secondary transition cosets reach the containing-octad A class. -/
theorem generatedFeasibleActualTransition_secondary_containing_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) = 4928 := by
  rw [generatedFeasibleActualTransition_secondary_cosets_eq_vectors]
  exact generatedFeasibleActualTransition_secondary_containing_vectors_card

/-- Exactly 42,240 genuine secondary transition cosets reach the outside-octad A class. -/
theorem generatedFeasibleActualTransition_secondary_outside_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleOutsideOctadDestination) = 42240 := by
  rw [generatedFeasibleActualTransition_secondary_cosets_eq_vectors]
  exact generatedFeasibleActualTransition_secondary_outside_vectors_card

/-- Exactly 45,056 genuine secondary transition cosets reach the odd A class. -/
theorem generatedFeasibleActualTransition_secondary_odd_card :
    Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      generatedFeasibleSecondaryOddDestination) = 45056 := by
  rw [generatedFeasibleActualTransition_secondary_cosets_eq_vectors]
  exact generatedFeasibleActualTransition_secondary_odd_vectors_card

/-- Actual containing-orbit size and reverse transition count obey the genuine balance equation. -/
theorem generatedFeasibleActualTransition_containing_secondary_equation :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination) *
        Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
          generatedFeasibleContainingOctadDestination
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 93150 * 4928 := by
  have h := generatedFeasibleActualTransition_reciprocity generatedFeasiblePhysicalRootPair
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
    generatedFeasibleContainingOctadDestination
  rw [generatedFeasibleActualTransition_secondary_containing_card] at h
  have hc : Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 93150 :=
    generatedFeasibleSecondaryLocalOrbit_card _
  rw [hc] at h
  exact h.symm

/-- Actual outside-orbit size and reverse transition count obey the genuine balance equation. -/
theorem generatedFeasibleActualTransition_outside_secondary_equation :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleOutsideOctadDestination) *
        Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
          generatedFeasibleOutsideOctadDestination
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 93150 * 42240 := by
  have h := generatedFeasibleActualTransition_reciprocity generatedFeasiblePhysicalRootPair
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
    generatedFeasibleOutsideOctadDestination
  rw [generatedFeasibleActualTransition_secondary_outside_card] at h
  have hc : Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 93150 :=
    generatedFeasibleSecondaryLocalOrbit_card _
  rw [hc] at h
  exact h.symm

/-- Actual odd-orbit size and reverse transition count obey the genuine balance equation. -/
theorem generatedFeasibleActualTransition_odd_secondary_equation :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleSecondaryOddDestination) *
        Nat.card (generatedFeasibleActualTransitionCosets generatedFeasiblePhysicalRootPair
          generatedFeasibleSecondaryOddDestination
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 93150 * 45056 := by
  have h := generatedFeasibleActualTransition_reciprocity generatedFeasiblePhysicalRootPair
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
    generatedFeasibleSecondaryOddDestination
  rw [generatedFeasibleActualTransition_secondary_odd_card] at h
  have hc : Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)) = 93150 :=
    generatedFeasibleSecondaryLocalOrbit_card _
  rw [hc] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
