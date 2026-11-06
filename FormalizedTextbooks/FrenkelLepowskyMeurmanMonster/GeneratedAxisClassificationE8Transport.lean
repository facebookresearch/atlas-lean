/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8CoordinateCatalog
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOctadNormEightFrameCount

/-! Actual lattice isometries transport both sides of the section-frame incidence. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine lattice map induces a bijection on integral submodules. -/
def generatedAxisE8SectionEquiv (g : leechIsomSubgroup) :
    Equiv.Perm (Submodule ℤ leechIntegral) :=
  (Submodule.orderIsoMapComap (leechIntegralAction g)).toEquiv

/-- On actual coordinate sections this bijection is the defined image section. -/
theorem generatedAxisE8SectionEquiv_coordinate (g : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) :
    generatedAxisE8SectionEquiv g (generatedAxisE8CoordinateSection c) =
      generatedAxisE8ImageSection g c := rfl

/-- The submodule bijections compose by the genuine group multiplication. -/
theorem generatedAxisE8SectionEquiv_mul (g h : leechIsomSubgroup)
    (S : Submodule ℤ leechIntegral) :
    generatedAxisE8SectionEquiv (g * h) S =
      generatedAxisE8SectionEquiv g (generatedAxisE8SectionEquiv h S) := by
  change S.map (leechIntegralAction (g * h)).toLinearMap =
    (S.map (leechIntegralAction h).toLinearMap).map (leechIntegralAction g).toLinearMap
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro u
  change leechIntegralAction (g * h) u = leechIntegralAction g (leechIntegralAction h u)
  rw [map_mul, LinearEquiv.mul_apply]

/-- The identity isometry fixes every integral section. -/
theorem generatedAxisE8SectionEquiv_one (S : Submodule ℤ leechIntegral) :
    generatedAxisE8SectionEquiv 1 S = S := by
  change S.map (leechIntegralAction 1).toLinearMap = S
  rw [map_one]
  change S.map (LinearMap.id : leechIntegral →ₗ[ℤ] leechIntegral) = S
  exact Submodule.map_id S

/-- Transport by an actual isometry preserves membership in the genuine section orbit. -/
theorem generatedAxisE8SectionEquiv_orbit (g : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) (S : Submodule ℤ leechIntegral) :
    generatedAxisE8SectionEquiv g S ∈ generatedAxisE8SectionOrbit c ↔
      S ∈ generatedAxisE8SectionOrbit c := by
  constructor
  · rintro ⟨h, hh⟩
    change generatedAxisE8ImageSection h c = generatedAxisE8SectionEquiv g S at hh
    refine ⟨g⁻¹ * h, ?_⟩
    change generatedAxisE8SectionEquiv (g⁻¹ * h) (generatedAxisE8CoordinateSection c) = S
    rw [generatedAxisE8SectionEquiv_mul]
    change generatedAxisE8SectionEquiv g⁻¹ (generatedAxisE8ImageSection h c) = S
    rw [hh, ← generatedAxisE8SectionEquiv_mul, inv_mul_cancel,
      generatedAxisE8SectionEquiv_one]
  · rintro ⟨h, hh⟩
    change generatedAxisE8ImageSection h c = S at hh
    refine ⟨g * h, ?_⟩
    change generatedAxisE8SectionEquiv (g * h) (generatedAxisE8CoordinateSection c) = _
    rw [generatedAxisE8SectionEquiv_mul]
    change generatedAxisE8SectionEquiv g (generatedAxisE8ImageSection h c) = _
    rw [hh]

/-- Actual section/frame incidence is preserved in both directions. -/
theorem generatedAxisE8_frame_transport (g : leechIsomSubgroup)
    (S : Submodule ℤ leechIntegral) (b : LeechModTwo) :
    leechModTwoAction g b ∈ generatedAxisE8FrameClasses (generatedAxisE8SectionEquiv g S) ↔
      b ∈ generatedAxisE8FrameClasses S := by
  constructor
  · rintro ⟨u, hu, hnu, hub⟩
    obtain ⟨v, hv, hgv⟩ := Submodule.mem_map.mp hu
    refine ⟨v, hv, ?_, ?_⟩
    · rw [← leechIntegralAction_squareSum g v]
      exact (congrArg (fun x : leechIntegral => leechSquareSum x.val) hgv).trans hnu
    · apply (leechModTwoAction g).injective
      change leechReduction (leechIntegralAction g v) = leechModTwoAction g b
      exact (congrArg leechReduction hgv).trans hub
  · rintro ⟨u, hu, hnu, hub⟩
    refine ⟨leechIntegralAction g u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩, ?_, ?_⟩
    · rw [leechIntegralAction_squareSum, hnu]
    · change leechModTwoAction g (leechReduction u) = leechModTwoAction g b
      rw [hub]

/-- The coordinate section's incidence classes are exactly the root count's
range of actual norm-eight lattice reductions. -/
theorem generatedAxisE8_coordinate_frameClasses (c : Fin 24 → ZMod 2) :
    generatedAxisE8FrameClasses (generatedAxisE8CoordinateSection c) =
      generatedOctadNormEightFrameClasses c := by
  ext b
  constructor
  · rintro ⟨u, hu, hnu, hub⟩
    exact ⟨⟨u, hu, hnu⟩, hub⟩
  · rintro ⟨⟨u, hu, hnu⟩, hub⟩
    exact ⟨u, hu, hnu, hub⟩

/-- Every actual section in a coordinate octad orbit contains exactly 135
actual frame classes, by a bijection induced by its actual isometry. -/
theorem generatedAxisE8_image_frameClasses_card (o : Fin 759) (g : leechIsomSubgroup) :
    Nat.card (generatedAxisE8FrameClasses (generatedAxisE8ImageSection g (golayOctadWord o))) =
      135 := by
  have E := (leechModTwoAction g).toEquiv.subtypeEquiv
    (fun b => (generatedAxisE8_frame_transport g (generatedAxisE8CoordinateSection
      (golayOctadWord o)) b).symm)
  have hcard := Nat.card_congr E
  change Nat.card (generatedAxisE8FrameClasses (generatedAxisE8CoordinateSection
      (golayOctadWord o))) = Nat.card (generatedAxisE8FrameClasses
        (generatedAxisE8ImageSection g (golayOctadWord o))) at hcard
  rw [← hcard, generatedAxisE8_coordinate_frameClasses]
  exact generatedOctad_frameClasses_card (golayOctadWord o)
    (golayOctadWord_mem_code o) (golayOctadWord_weight o)

/-- The actual section orbit fiber through an arbitrary frame class. -/
def generatedAxisE8SectionsThrough (c : Fin 24 → ZMod 2) (b : LeechModTwo) :
    Set (Submodule ℤ leechIntegral) :=
  {S | S ∈ generatedAxisE8SectionOrbit c ∧ b ∈ generatedAxisE8FrameClasses S}

/-- The actual submodule bijection transports section fibers over frame classes. -/
def generatedAxisE8SectionsThroughEquiv (g : leechIsomSubgroup)
    (c : Fin 24 → ZMod 2) (b : LeechModTwo) :
    generatedAxisE8SectionsThrough c b ≃
      generatedAxisE8SectionsThrough c (leechModTwoAction g b) :=
  (generatedAxisE8SectionEquiv g).subtypeEquiv (fun S => by
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [generatedAxisE8SectionEquiv_orbit, generatedAxisE8_frame_transport])

/-- Every actual frame-orbit class is incident with exactly 759 actual sections. -/
theorem generatedAxisE8SectionsThrough_card (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ MulAction.orbit leechIsomSubgroup
      (leechReduction (leechCoordinateFrameLattice 0))) :
    Nat.card (generatedAxisE8SectionsThrough (golayOctadWord o) b) = 759 := by
  obtain ⟨g, hg⟩ := hb
  change leechModTwoAction g (leechReduction (leechCoordinateFrameLattice 0)) = b at hg
  rw [← hg, ← Nat.card_congr (generatedAxisE8SectionsThroughEquiv g (golayOctadWord o)
    (leechReduction (leechCoordinateFrameLattice 0)))]
  exact generatedAxisE8RootedSections_card o

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
