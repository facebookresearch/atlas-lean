/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenClassIdentification

/-! The full actual one-quarter class stabilizer, identified through a genuine A orbit relation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The stabilizer of the entire actual one-quarter destination inside the original A group. -/
def generatedFeasibleContainingSixteenDestinationStabilizer :
    Subgroup (localAxisStabilizer generatedFeasiblePhysicalRootPair) :=
  MulAction.stabilizer (localAxisStabilizer generatedFeasiblePhysicalRootPair)
    generatedFeasibleContainingSixteenDestination

/-- Genuine whole-vector class identification conjugates the complete one-quarter stabilizer
onto the already proved odd-class stabilizer. -/
def generatedFeasibleContainingSixteenStabilizerEquiv :
    generatedFeasibleContainingSixteenDestinationStabilizer ≃*
      generatedFeasibleOddSourceDestinationStabilizer :=
  MulAction.stabilizerEquivStabilizerOfOrbitRel
    (Quotient.exact generatedFeasibleContainingSixteen_class_eq_odd)

/-- The full actual one-quarter destination stabilizer has order169,114,337,280. -/
theorem generatedFeasibleContainingSixteenDestinationStabilizer_card :
    Nat.card generatedFeasibleContainingSixteenDestinationStabilizer = 169114337280 := by
  rw [Nat.card_congr generatedFeasibleContainingSixteenStabilizerEquiv.toEquiv]
  exact generatedFeasibleOddSourceDestinationStabilizer_card

/-- Its actual index in the original A group is4,196,966,400. -/
theorem generatedFeasibleContainingSixteenDestinationStabilizer_index :
    generatedFeasibleContainingSixteenDestinationStabilizer.index = 4196966400 := by
  have h := generatedFeasibleContainingSixteenDestinationStabilizer.card_mul_index
  rw [generatedFeasibleContainingSixteenDestinationStabilizer_card,
    localAxisStabilizer_card_of_co1_card _ co1_card_exact] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
