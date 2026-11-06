/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsBoundedCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsBoundedCoverage

/-! Exact counts of intrinsic singular four-spaces and actual selected-section
fifteen-frame systems, with finite coverage checked by the ordinary kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- An exact finite parametrization of genuine frame systems in the selected E8 section. -/
def generatedAxisE8ActualFrameSystemsEquivCandidates : Fin 270 ≃
    generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) :=
  (generatedAxisE8FrameSystemsBoundedEquivCandidates
    generatedAxisE8FrameCandidateBoundedCoverage_certificate).trans generatedAxisE8FrameSystemsEquiv

/-- The270 displayed candidates exhaust the genuine intrinsic singular four-spaces. -/
theorem generatedAxisE8FrameSystems_complete
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (hW : W ∈ generatedAxisE8IntrinsicFrameSystems) :
    ∃ k : Fin 270, generatedAxisE8FrameSystemCandidate k = W :=
  generatedAxisE8FrameSystems_complete_of_bounded_coverage
    generatedAxisE8FrameCandidateBoundedCoverage_certificate W hW

/-- There are exactly270 totally singular sixteen-element root-coordinate spaces. -/
theorem generatedAxisE8IntrinsicFrameSystems_card :
    Nat.card generatedAxisE8IntrinsicFrameSystems = 270 :=
  generatedAxisE8IntrinsicFrameSystems_card_of_bounded_coverage
    generatedAxisE8FrameCandidateBoundedCoverage_certificate

/-- The actual selected E8 section has exactly270 genuine fifteen-frame systems. -/
theorem generatedAxisE8FrameSystems_card :
    Nat.card (generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) = 270 :=
  generatedAxisE8FrameSystems_card_of_bounded_coverage
    generatedAxisE8FrameCandidateBoundedCoverage_certificate

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
