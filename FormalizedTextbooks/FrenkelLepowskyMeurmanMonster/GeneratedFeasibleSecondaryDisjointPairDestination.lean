/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryDisjointPairOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFeasibleCosets

/-! Original triality destination for the actual disjoint coordinate-pair secondary sector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original extra-generator image of the genuine disjoint minus-pair prototype axis. -/
def generatedFeasibleDisjointPairDestination : GriessSpace :=
  sExtra (conwayShortAxis generatedFeasibleDisjointPairPrototypeLabel 0)

/-- Every actual disjoint-pair secondary input has triality image in the first-axis stabilizer
orbit of its source-defined prototype destination. -/
theorem generatedFeasibleDisjointPair_triality_destination (z : Fin 2 × Fin 276)
    (hz : z ∈ generatedFeasibleDisjointPairLabels) (c : ZMod 2) :
    ∃ h : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      rhoLocal h.val (sExtra (conwayShortAxis (Sum.inl z) c)) =
        generatedFeasibleDisjointPairDestination := by
  obtain ⟨n, hn⟩ := generatedFeasibleDisjointPair_to_prototype z hz c 0
  let n' : localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair :=
    ⟨⟨n.val, n.property.1⟩, n.property.2⟩
  obtain ⟨h, hh⟩ := localFeasibleTransition_triality_orbit _ n' (conwayShortAxis (Sum.inl z) c)
  refine ⟨h, ?_⟩
  change rhoLocal h.val (sExtra (conwayShortAxis (Sum.inl z) c)) =
    sExtra (conwayShortAxis generatedFeasibleDisjointPairPrototypeLabel 0)
  change rhoLocal h.val (sExtra (conwayShortAxis (Sum.inl z) c)) =
    sExtra (rhoLocal n.val (conwayShortAxis (Sum.inl z) c)) at hh
  rwa [hn] at hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
