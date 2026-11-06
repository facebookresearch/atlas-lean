/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemOrder

/-! The full original selected-section group acts on genuine frame systems.
Its candidate14 orbit is counted through the actual simultaneous stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- The section and simultaneous stabilizers are nested actual subgroup carriers.
set_option maxRecDepth 10000

/-- The full actual group fixing the selected integral E8 section. -/
abbrev generatedAxisE8FrameSystemSectionGroup :=
  generatedAxisE8SectionStabilizer (golayOctadWord generatedFifthFlagOctad)

/-- A full selected-section orbit remains in the genuine sixteen-element system carrier. -/
theorem generatedAxisE8FrameSystems_orbit_subset
    (W : Submodule (ZMod 2) LeechModTwo)
    (hW : W ∈ generatedAxisE8FrameSystems
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad))) :
    MulAction.orbit generatedAxisE8FrameSystemSectionGroup W ⊆
      generatedAxisE8FrameSystems
        (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  rintro V ⟨g, rfl⟩
  exact generatedAxisE8FrameSystems_section_action generatedFifthFlagOctad g W hW

/-- Restricting to the full section group gives the same actual simultaneous stabilizer. -/
def generatedAxisE8FrameSystemSelectedStabilizerEquiv :
    MulAction.stabilizer generatedAxisE8FrameSystemSectionGroup
      (generatedAxisE8ActualFrameSystemCandidate 14) ≃ generatedFifthFrameSystemStabilizer where
  toFun g := ⟨g.val.val, by
    rw [generatedFifthFrameSystemStabilizer, generatedAxisE8FrameSystemStabilizer_mem]
    refine ⟨(generatedAxisE8SectionStabilizer_mem _ _).mp g.val.property, ?_⟩
    have h := g.property
    change (generatedAxisE8ActualFrameSystemCandidate 14).map
      (leechModTwoAction g.val.val).toLinearMap = generatedAxisE8ActualFrameSystemCandidate 14 at h
    simpa only [generatedFifthFrameSystem_actual_candidate] using h⟩
  invFun g := ⟨⟨g.val, by
    rw [generatedAxisE8SectionStabilizer_mem]
    exact ((generatedAxisE8FrameSystemStabilizer_mem _ _ _).mp g.property).1⟩, by
    change (generatedAxisE8ActualFrameSystemCandidate 14).map
      (leechModTwoAction g.val).toLinearMap = generatedAxisE8ActualFrameSystemCandidate 14
    rw [← generatedFifthFrameSystem_actual_candidate]
    exact ((generatedAxisE8FrameSystemStabilizer_mem _ _ _).mp g.property).2⟩
  left_inv g := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl

/-- The full actual selected-section orbit of the original fifth frame system has135 elements. -/
theorem generatedAxisE8FrameSystemCandidate_orbit_card_fourteen :
    Nat.card (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (generatedAxisE8ActualFrameSystemCandidate 14)) = 135 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedAxisE8FrameSystemSectionGroup (generatedAxisE8ActualFrameSystemCandidate 14))
  rw [Nat.card_prod, Nat.card_congr generatedAxisE8FrameSystemSelectedStabilizerEquiv,
    generatedFifthFrameSystem_stabilizer_card,
    generatedAxisE8_sectionStabilizer_card generatedFifthFlagOctad] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 1321205760)
    (h.trans (by decide : 178362777600 = 135 * 1321205760))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
