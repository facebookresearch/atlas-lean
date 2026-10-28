/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameFlagsStabilizer

/-! Actual frame fibers and monomial recognition inside coordinate E8 sections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original norm-eight frame class is incident with every actual coordinate octad section. -/
theorem generatedAxisE8FrameFlags_frame_zero_incident (o : Fin 759) :
    leechReduction (leechCoordinateFrameLattice 0) ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o)) :=
  (generatedAxisE8_coordinate_octad_rooted o o).2

/-- Every actual incident frame is reached by the entire coordinate-section stabilizer. -/
theorem generatedAxisE8FrameFlags_local_orbit_eq (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    MulAction.orbit (generatedAxisE8SectionStabilizer (golayOctadWord o)) b =
      generatedAxisE8FrameClasses (generatedAxisE8CoordinateSection (golayOctadWord o)) := by
  ext c
  constructor
  · rintro ⟨e, he⟩
    change leechModTwoAction e.val b = c at he
    have h := (generatedAxisE8_frame_transport e.val
      (generatedAxisE8CoordinateSection (golayOctadWord o)) b).mpr hb
    change leechModTwoAction e.val b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8ImageSection e.val (golayOctadWord o)) at h
    rw [(generatedAxisE8SectionStabilizer_mem _ e.val).mp e.property, he] at h
    exact h
  · intro hc
    obtain ⟨e, _, hpres, he⟩ := generatedAxisE8FrameFlags_coordinate_transitive o b c hb hc
    exact ⟨⟨e, (generatedAxisE8SectionStabilizer_mem _ e).mpr
      (generatedAxisE8_preserving_image _ e hpres)⟩, he⟩

/-- Each actual section-preserving frame orbit consists of exactly 135 classes. -/
theorem generatedAxisE8FrameFlags_local_orbit_card (o : Fin 759) (b : LeechModTwo)
    (hb : b ∈ generatedAxisE8FrameClasses
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Nat.card (MulAction.orbit (generatedAxisE8SectionStabilizer (golayOctadWord o)) b) =
      135 := by
  rw [generatedAxisE8FrameFlags_local_orbit_eq o b hb]
  have h := generatedAxisE8_image_frameClasses_card o 1
  change Nat.card (generatedAxisE8FrameClasses (generatedAxisE8SectionEquiv 1
    (generatedAxisE8CoordinateSection (golayOctadWord o)))) = 135 at h
  rwa [generatedAxisE8SectionEquiv_one] at h

/-- A genuine Golay monomial sends the original section to its actual permuted code support. -/
theorem generatedAxisE8FrameFlags_monomial_section_image (o : Fin 759)
    (d : golayCode) (p : golayAutomorphismSubgroup) :
    generatedAxisE8ImageSection (golaySignIsometry d * golayPermutationIsometry p)
      (golayOctadWord o) =
        generatedAxisE8CoordinateSection (golayPermute p.val (golayOctadWord o)) := by
  rw [generatedAxisE8ImageSection_mul, generatedAxisE8_permutation_image]
  exact generatedAxisE8_preserving_image _ _ (generatedAxisE8_sign_preserves _ d)

/-- Through frame zero, the entire actual flag stabilizer is the original Golay-sign/octad fixer. -/
theorem generatedAxisE8FrameFlags_monomial_mem_iff (o : Fin 759) (g : leechIsomSubgroup) :
    g ∈ generatedAxisE8FrameFlagsStabilizer o
      (leechReduction (leechCoordinateFrameLattice 0)) ↔
    ∃ d : golayCode, ∃ p : golayAutomorphismSubgroup,
      golayPermute p.val (golayOctadWord o) = golayOctadWord o ∧
        golaySignIsometry d * golayPermutationIsometry p = g := by
  rw [generatedAxisE8FrameFlags_frame_zero_mem_iff]
  constructor
  · rintro ⟨hsection, d, p, rfl⟩
    refine ⟨d, p, ?_, rfl⟩
    apply generatedAxisE8CoordinateSection_injective
    rw [← generatedAxisE8FrameFlags_monomial_section_image]
    exact (generatedAxisE8SectionStabilizer_mem _ _).mp hsection
  · rintro ⟨d, p, hp, rfl⟩
    constructor
    · rw [generatedAxisE8SectionStabilizer_mem,
        generatedAxisE8FrameFlags_monomial_section_image, hp]
    · exact ⟨d, p, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
