/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryContainingOctadOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFeasibleCosets

/-! Actual triality destination of the containing-pair secondary octad sector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original extra-generator image of the actual positive standard octad axis. -/
def generatedFeasibleContainingOctadDestination : GriessSpace :=
  sExtra (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0)

/-- Every actual containing-pair secondary input has triality image in the first-axis
stabilizer orbit of the source-defined standard octad destination. -/
theorem generatedFeasibleContainingOctad_triality_destination (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels 0) (c : ZMod 2) :
    ∃ h : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      rhoLocal h.val (sExtra (conwayShortAxis r c)) =
        generatedFeasibleContainingOctadDestination := by
  obtain ⟨n, hn⟩ := generatedFeasibleContainingOctad_to_prototype r hr c 0
  let n' : localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair :=
    ⟨⟨n.val, n.property.1⟩, n.property.2⟩
  obtain ⟨h, hh⟩ := localFeasibleTransition_triality_orbit _ n' (conwayShortAxis r c)
  refine ⟨h, ?_⟩
  change rhoLocal h.val (sExtra (conwayShortAxis r c)) =
    sExtra (conwayShortAxis generatedFeasibleContainingOctadPrototypeLabel 0)
  change rhoLocal h.val (sExtra (conwayShortAxis r c)) =
    sExtra (rhoLocal n.val (conwayShortAxis r c)) at hh
  rwa [hn] at hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
