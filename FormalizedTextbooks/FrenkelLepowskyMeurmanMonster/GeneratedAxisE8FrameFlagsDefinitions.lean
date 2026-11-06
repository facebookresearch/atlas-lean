/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8SectionStabilizerCount

/-! Genuine E8-section and norm-eight frame-class incidence flags. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- An actual E8 section together with an actual norm-eight frame class inside it. -/
def generatedAxisE8FrameFlags (o : Fin 759) :=
  Σ S : generatedAxisE8SectionOrbit (golayOctadWord o), generatedAxisE8FrameClasses S.val

/-- The genuine section-frame incidence has exactly 6293912625 flags. -/
theorem generatedAxisE8FrameFlags_card (o : Fin 759) :
    Nat.card (generatedAxisE8FrameFlags o) = 6293912625 := by
  let X := generatedAxisE8SectionOrbit (golayOctadWord o)
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
  have hs (S : X) : Nat.card (generatedAxisE8FrameClasses S.val) = 135 := by
    obtain ⟨g, hg⟩ := S.property
    change generatedAxisE8ImageSection g (golayOctadWord o) = S.val at hg
    rw [← hg]
    exact generatedAxisE8_image_frameClasses_card o g
  change Nat.card (Σ S : X, generatedAxisE8FrameClasses S.val) = _
  rw [Nat.card_sigma]
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  change Nat.card (generatedAxisE8SectionOrbit (golayOctadWord o)) * 135 = _
  rw [generatedAxisE8_sectionOrbit_card]

/-- The full coordinate-section preserving isometries reach every incident frame class. -/
theorem generatedAxisE8FrameFlags_coordinate_transitive (o : Fin 759) (b c : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o)))
    (hc : c ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    ∃ e : leechIsomSubgroup, e ∈ leechConcreteGeneratorSubgroup ∧
      generatedOctadPreserves (golayOctadWord o) e ∧ leechModTwoAction e b = c := by
  obtain ⟨u, hu, hnu, hub⟩ := hb
  obtain ⟨v, hv, hnv, hvc⟩ := hc
  obtain ⟨e, he, hpres, huv⟩ := generatedOctad_normEight_transitive (golayOctadWord o)
    (golayOctadWord_mem_code o) (golayOctadWord_weight o) u v hu hv hnu hnv
  refine ⟨e, he, hpres, ?_⟩
  rw [← hub, ← hvc]
  change leechReduction (leechIntegralAction e u) = leechReduction v
  rw [huv]

/-- Every genuine section-frame flag is reached from any incident coordinate flag. -/
theorem generatedAxisE8FrameFlags_transitive (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o)))
    (S : Submodule ℤ leechIntegral) (t : LeechModTwo)
    (hS : S ∈ generatedAxisE8SectionOrbit (golayOctadWord o))
    (ht : t ∈ generatedAxisE8FrameClasses S) :
    ∃ g : leechIsomSubgroup, generatedAxisE8ImageSection g (golayOctadWord o) = S ∧
      leechModTwoAction g b = t := by
  obtain ⟨a, ha⟩ := hS
  change generatedAxisE8ImageSection a (golayOctadWord o) = S at ha
  let c := leechModTwoAction a⁻¹ t
  have hct : leechModTwoAction a c = t := by
    simp [c, map_inv]
  have hc : c ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o)) := by
    apply (generatedAxisE8_frame_transport a
      (generatedAxisE8CoordinateSection (golayOctadWord o)) c).mp
    rw [hct]
    change t ∈ generatedAxisE8FrameClasses (generatedAxisE8ImageSection a (golayOctadWord o))
    rw [ha]
    exact ht
  obtain ⟨e, _, he, hec⟩ := generatedAxisE8FrameFlags_coordinate_transitive o b c hb hc
  refine ⟨a * e, ?_, ?_⟩
  · rw [generatedAxisE8ImageSection_mul_preserving a e _ he, ha]
  · rw [map_mul, LinearEquiv.mul_apply, hec, hct]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
