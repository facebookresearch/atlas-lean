/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameFlagsDefinitions

/-! The genuine E8-section/frame orbit equals the complete actual incidence set. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual orbit of a coordinate section and an incident binary frame class. -/
def generatedAxisE8FrameFlagsOrbit (o : Fin 759) (b : LeechModTwo) :
    Set (Submodule ℤ leechIntegral × LeechModTwo) :=
  Set.range (fun g : leechIsomSubgroup =>
    (generatedAxisE8ImageSection g (golayOctadWord o), leechModTwoAction g b))

/-- The actual pair orbit is bijective with the full section-frame incidence. -/
def generatedAxisE8FrameFlagsOrbitEquiv (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    generatedAxisE8FrameFlagsOrbit o b ≃ generatedAxisE8FrameFlags o where
  toFun x := ⟨⟨x.val.1, by
    obtain ⟨g, hg⟩ := x.property
    exact ⟨g, congrArg Prod.fst hg⟩⟩, ⟨x.val.2, by
    obtain ⟨g, hg⟩ := x.property
    have h := (generatedAxisE8_frame_transport g
      (generatedAxisE8CoordinateSection (golayOctadWord o)) b).mpr hb
    change leechModTwoAction g b ∈
      generatedAxisE8FrameClasses (generatedAxisE8ImageSection g (golayOctadWord o)) at h
    change (generatedAxisE8ImageSection g (golayOctadWord o), leechModTwoAction g b) =
      x.val at hg
    have h1 := congrArg Prod.fst hg
    have h2 := congrArg Prod.snd hg
    change generatedAxisE8ImageSection g (golayOctadWord o) = x.val.1 at h1
    change leechModTwoAction g b = x.val.2 at h2
    rw [h1, h2] at h
    exact h⟩⟩
  invFun x := ⟨(x.1.val, x.2.val), by
    obtain ⟨g, hS, ht⟩ := generatedAxisE8FrameFlags_transitive o b hb
      x.1.val x.2.val x.1.property x.2.property
    exact ⟨g, Prod.ext hS ht⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by cases x; rfl

/-- Each actual incident coordinate section-frame pair has exactly 6293912625 images. -/
theorem generatedAxisE8FrameFlagsOrbit_card (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Nat.card (generatedAxisE8FrameFlagsOrbit o b) = 6293912625 := by
  rw [Nat.card_congr (generatedAxisE8FrameFlagsOrbitEquiv o b hb),
    generatedAxisE8FrameFlags_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
