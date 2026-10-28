/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryOddOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFeasibleCosets

/-! An actual triality destination for every physical secondary odd input. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual extra-generator image of the original odd prototype axis. -/
def generatedFeasibleSecondaryOddDestination : GriessSpace :=
  sExtra (conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0)

/-- Every actual secondary odd input has triality image in the first-axis-stabilizer
orbit of the source-defined prototype destination. -/
theorem generatedFeasibleSecondaryOdd_triality_destination (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels 2) (c : ZMod 2) :
    ∃ h : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      rhoLocal h.val (sExtra (conwayShortAxis r c)) =
        generatedFeasibleSecondaryOddDestination := by
  obtain ⟨n, hn⟩ := generatedFeasibleSecondaryOdd_to_prototype r hr c 0
  let n' : localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair :=
    ⟨⟨n.val, n.property.1⟩, n.property.2⟩
  obtain ⟨h, hh⟩ := localFeasibleTransition_triality_orbit _ n' (conwayShortAxis r c)
  refine ⟨h, ?_⟩
  change rhoLocal h.val (sExtra (conwayShortAxis r c)) =
    sExtra (conwayShortAxis generatedFeasibleSecondaryOddPrototypeLabel 0)
  change rhoLocal h.val (sExtra (conwayShortAxis r c)) =
    sExtra (rhoLocal n.val (conwayShortAxis r c)) at hh
  rwa [hn] at hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
