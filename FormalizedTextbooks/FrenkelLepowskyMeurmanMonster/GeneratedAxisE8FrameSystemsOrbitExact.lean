/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitFamilies

/-! The full original selected-section action has two135-element system orbits,
with the actual source candidates0 and14 as representatives. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Candidate0 has135 distinct images under the full original section group. -/
theorem generatedAxisE8FrameSystemCandidate_orbit_card_zero :
    Nat.card (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (generatedAxisE8ActualFrameSystemCandidate 0)) = 135 := by
  rw [← generatedAxisE8FrameSystemOrbitFamily_zero_eq_orbit]
  exact generatedAxisE8FrameSystemOrbitFamily_card 0

/-- The entire actual270-system carrier is the union of the two full original orbits. -/
theorem generatedAxisE8FrameSystems_two_orbits :
    generatedAxisE8FrameSystems
        (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) =
      MulAction.orbit generatedAxisE8FrameSystemSectionGroup
          (generatedAxisE8ActualFrameSystemCandidate 0) ∪
        MulAction.orbit generatedAxisE8FrameSystemSectionGroup
          (generatedAxisE8ActualFrameSystemCandidate 14) := by
  rw [← generatedAxisE8FrameSystemOrbitFamily_zero_eq_orbit,
    ← generatedAxisE8FrameSystemOrbitFamily_one_eq_orbit]
  exact generatedAxisE8FrameSystemOrbitFamily_union.symm

/-- The two actual full section-group orbits are disjoint. -/
theorem generatedAxisE8FrameSystems_two_orbits_disjoint :
    Disjoint (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
      (generatedAxisE8ActualFrameSystemCandidate 0))
      (MulAction.orbit generatedAxisE8FrameSystemSectionGroup
        (generatedAxisE8ActualFrameSystemCandidate 14)) := by
  rw [← generatedAxisE8FrameSystemOrbitFamily_zero_eq_orbit,
    ← generatedAxisE8FrameSystemOrbitFamily_one_eq_orbit]
  exact generatedAxisE8FrameSystemOrbitFamily_disjoint 0 1 (by decide)

/-- Fixing an entire system in the section group equals fixing both actual geometric objects. -/
def generatedAxisE8FrameSystemRestrictedStabilizerEquiv
    (W : Submodule (ZMod 2) LeechModTwo) :
    MulAction.stabilizer generatedAxisE8FrameSystemSectionGroup W ≃
      generatedAxisE8FrameSystemStabilizer generatedFifthFlagOctad W where
  toFun g := ⟨g.val.val, by
    rw [generatedAxisE8FrameSystemStabilizer_mem]
    exact ⟨(generatedAxisE8SectionStabilizer_mem _ _).mp g.val.property, g.property⟩⟩
  invFun g := ⟨⟨g.val, (generatedAxisE8SectionStabilizer_mem _ _).mpr
    ((generatedAxisE8FrameSystemStabilizer_mem _ _ _).mp g.property).1⟩,
    ((generatedAxisE8FrameSystemStabilizer_mem _ _ _).mp g.property).2⟩
  left_inv g := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl

/-- The full actual section/candidate0 simultaneous stabilizer has order1321205760. -/
theorem generatedAxisE8FrameSystemCandidate_zero_stabilizer_card :
    Nat.card (generatedAxisE8FrameSystemStabilizer generatedFifthFlagOctad
      (generatedAxisE8ActualFrameSystemCandidate 0)) = 1321205760 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedAxisE8FrameSystemSectionGroup (generatedAxisE8ActualFrameSystemCandidate 0))
  rw [Nat.card_prod, generatedAxisE8FrameSystemCandidate_orbit_card_zero,
    Nat.card_congr (generatedAxisE8FrameSystemRestrictedStabilizerEquiv _),
    generatedAxisE8_sectionStabilizer_card generatedFifthFlagOctad] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 135)
    (h.trans (by decide : 178362777600 = 135 * 1321205760))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
