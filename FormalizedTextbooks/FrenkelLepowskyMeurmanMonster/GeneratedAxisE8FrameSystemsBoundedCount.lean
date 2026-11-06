/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsBoundedCompleteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsMaskRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoordinates

/-! A finite coverage certificate determines the exact number of genuine
sixteen-element singular spaces and hence of actual selected-section frame systems. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A checked cover makes the displayed intrinsic candidate parametrization bijective. -/
def generatedAxisE8FrameSystemsBoundedEquivCandidates
    (hcover : ∀ a : Fin 32, generatedAxisE8FrameCandidateCoverageAt
      ⟨a.val, by omega⟩) :
    Fin 270 ≃ generatedAxisE8IntrinsicFrameSystems :=
  Equiv.ofBijective
    (fun k => ⟨generatedAxisE8FrameSystemCandidate k,
      generatedAxisE8FrameSystemCandidate_mem k⟩)
    ⟨fun _ _ h => generatedAxisE8FrameSystemCandidate_injective
      (congrArg Subtype.val h), by
      intro W
      obtain ⟨k, hk⟩ := generatedAxisE8FrameSystems_complete_of_bounded_coverage
        hcover W.val W.property
      exact ⟨k, Subtype.ext hk⟩⟩

/-- Coverage and the independently checked distinctness give exactly270 intrinsic systems. -/
theorem generatedAxisE8IntrinsicFrameSystems_card_of_bounded_coverage
    (hcover : ∀ a : Fin 32, generatedAxisE8FrameCandidateCoverageAt
      ⟨a.val, by omega⟩) :
    Nat.card generatedAxisE8IntrinsicFrameSystems = 270 := by
  exact (Nat.card_congr (generatedAxisE8FrameSystemsBoundedEquivCandidates hcover)).symm.trans
    (Nat.card_fin 270)

/-- The actual selected E8 section has exactly270 systems once the finite cover is checked. -/
theorem generatedAxisE8FrameSystems_card_of_bounded_coverage
    (hcover : ∀ a : Fin 32, generatedAxisE8FrameCandidateCoverageAt
      ⟨a.val, by omega⟩) :
    Nat.card (generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) = 270 := by
  rw [generatedAxisE8FrameSystems_card_intrinsic]
  exact generatedAxisE8IntrinsicFrameSystems_card_of_bounded_coverage hcover

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
