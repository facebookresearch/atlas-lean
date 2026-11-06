/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Transport

/-! Double-counting the actual section/frame incidence gives the E8-section orbit size. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Exchanging the two actual incidence coordinates gives a genuine bijection. -/
def generatedAxisE8IncidenceEquiv (o : Fin 759) :
    (Σ S : generatedAxisE8SectionOrbit (golayOctadWord o),
      generatedAxisE8FrameClasses S.val) ≃
    (Σ b : MulAction.orbit leechIsomSubgroup
      (leechReduction (leechCoordinateFrameLattice 0)),
      generatedAxisE8SectionsThrough (golayOctadWord o) b.val) where
  toFun x := ⟨⟨x.2.val, by
    obtain ⟨g, hg⟩ := x.1.property
    change generatedAxisE8ImageSection g (golayOctadWord o) = x.1.val at hg
    apply generatedAxisE8FrameClasses_subset_frame_orbit (golayOctadWord o) g
    rw [hg]
    exact x.2.property⟩,
    ⟨x.1.val, x.1.property, x.2.property⟩⟩
  invFun y := ⟨⟨y.2.val, y.2.property.1⟩, ⟨y.1.val, y.2.property.2⟩⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl

/-- The full orbit of an actual coordinate E8 section under actual lattice
isometries contains precisely 46,621,575 sections. -/
theorem generatedAxisE8_sectionOrbit_card (o : Fin 759) :
    Nat.card (generatedAxisE8SectionOrbit (golayOctadWord o)) = 46621575 := by
  classical
  let X := generatedAxisE8SectionOrbit (golayOctadWord o)
  let B := MulAction.orbit leechIsomSubgroup
    (leechReduction (leechCoordinateFrameLattice 0))
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let : Finite LeechModTwo := Finite.of_injective
    leechHyperbolicCoordinates leechHyperbolicCoordinates.injective
  let f : leechIsomSubgroup → X := fun g =>
    ⟨generatedAxisE8ImageSection g (golayOctadWord o), ⟨g, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨S, g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  let : Finite X := Finite.of_surjective f hf
  let : Fintype X := Fintype.ofFinite X
  let : Fintype B := Fintype.ofFinite B
  let (b : B) : Finite (generatedAxisE8SectionsThrough (golayOctadWord o) b.val) :=
    Finite.of_injective
      (fun S : generatedAxisE8SectionsThrough (golayOctadWord o) b.val =>
        (⟨S.val, S.property.1⟩ : X)) (fun _ _ h =>
          Subtype.ext (congrArg (fun x : X => x.val) h))
  have hs (S : X) : Nat.card (generatedAxisE8FrameClasses S.val) = 135 := by
    obtain ⟨g, hg⟩ := S.property
    change generatedAxisE8ImageSection g (golayOctadWord o) = S.val at hg
    rw [← hg]
    exact generatedAxisE8_image_frameClasses_card o g
  have hb (b : B) : Nat.card (generatedAxisE8SectionsThrough (golayOctadWord o) b.val) =
      759 := generatedAxisE8SectionsThrough_card o b.val b.property
  have h : Nat.card X * 135 = Nat.card B * 759 := by
    calc
      Nat.card X * 135 = ∑ S : X, Nat.card (generatedAxisE8FrameClasses S.val) := by
        simp only [hs]
        simp [Nat.card_eq_fintype_card]
      _ = Nat.card (Σ S : X, generatedAxisE8FrameClasses S.val) := Nat.card_sigma.symm
      _ = Nat.card (Σ b : B, generatedAxisE8SectionsThrough (golayOctadWord o) b.val) :=
        Nat.card_congr (generatedAxisE8IncidenceEquiv o)
      _ = ∑ b : B, Nat.card (generatedAxisE8SectionsThrough (golayOctadWord o) b.val) :=
        Nat.card_sigma
      _ = Nat.card B * 759 := by
        simp only [hb]
        simp [Nat.card_eq_fintype_card]
  have hB : Nat.card B = 8292375 := leechFrameClass_orbit_card
  rw [hB] at h
  change Nat.card X = 46621575
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
