/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Rooted
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection

/-! Exact coordinate-section coverage of the actual rooted E8 section orbit. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A positive frame vector belongs to a coordinate section exactly when
the corresponding binary code coordinate is nonzero. -/
theorem generatedAxisE8_frame_mem_iff (c : Fin 24 → ZMod 2) (i : Fin 24) :
    leechCoordinateFrameLattice i ∈ generatedAxisE8CoordinateSection c ↔ c i ≠ 0 := by
  constructor
  · intro h hi
    have hz := h i hi
    norm_num [leechCoordinateFrameLattice, leechCoordinateFrameVector] at hz
  · exact generatedAxisE8_frame_supported c i

/-- Different binary supports give different genuine integral sections. -/
theorem generatedAxisE8CoordinateSection_injective :
    Function.Injective generatedAxisE8CoordinateSection := by
  intro c d he
  have hbit : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide +kernel
  funext i
  apply hbit
  have hi := congrArg (fun S : Submodule ℤ leechIntegral => leechCoordinateFrameLattice i ∈ S) he
  rw [propext (generatedAxisE8_frame_mem_iff c i),
    propext (generatedAxisE8_frame_mem_iff d i)] at hi
  exact not_iff_not.mp (iff_of_eq hi)

/-- Actual Golay octads have at least one physical support coordinate. -/
theorem generatedAxisE8_octad_support_nonempty (o : Fin 759) :
    ∃ i : Fin 24, golayOctadWord o i ≠ 0 := by
  by_contra! h
  have he : golayOctadWord o = 0 := funext h
  have hw := golayOctadWord_weight o
  rw [he] at hw
  norm_num at hw

/-- The already proved five-point Golay action transports any coordinate
octad section to any other, through genuine permutation isometries. -/
theorem generatedAxisE8_octad_permutation (o t : Fin 759) :
    ∃ p : golayAutomorphismSubgroup, golayPermute p.val (golayOctadWord o) = golayOctadWord t := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard (golayOctadWord o)
    (golayOctadWord_mem_code o) (golayOctadWord_weight o)
  obtain ⟨q, hq⟩ := golayOctad_to_standard (golayOctadWord t)
    (golayOctadWord_mem_code t) (golayOctadWord_weight t)
  refine ⟨q⁻¹ * p, ?_⟩
  funext i
  have hx := congrFun hp (q.val i)
  have hy := congrFun hq (q.val i)
  change golayOctadWord o (p.val.symm (q.val i)) = _ at hx
  change golayOctadWord t (q.val.symm (q.val i)) = _ at hy
  rw [q.val.symm_apply_apply] at hy
  change golayOctadWord o (p.val.symm (q.val i)) = golayOctadWord t i
  exact hx.trans hy.symm

/-- Every coordinate octad section is in the actual section orbit of the
initial octad and contains the actual distinguished frame class. -/
theorem generatedAxisE8_coordinate_octad_rooted (o t : Fin 759) :
    generatedAxisE8CoordinateSection (golayOctadWord t) ∈
        generatedAxisE8SectionOrbit (golayOctadWord o) ∧
      leechReduction (leechCoordinateFrameLattice 0) ∈
        generatedAxisE8FrameClasses (generatedAxisE8CoordinateSection (golayOctadWord t)) := by
  constructor
  · obtain ⟨p, hp⟩ := generatedAxisE8_octad_permutation o t
    refine ⟨golayPermutationIsometry p, ?_⟩
    change generatedAxisE8ImageSection (golayPermutationIsometry p) (golayOctadWord o) = _
    rw [generatedAxisE8_permutation_image, hp]
  · obtain ⟨i, hi⟩ := generatedAxisE8_octad_support_nonempty t
    exact ⟨leechCoordinateFrameLattice i, generatedAxisE8_frame_supported _ i hi,
      leechCoordinateFrameVector_square i, leechFrame_reduction_eq i⟩

/-- The actual section orbit fiber over the distinguished frame class. -/
def generatedAxisE8RootedSections (o : Fin 759) : Set (Submodule ℤ leechIntegral) :=
  {S | S ∈ generatedAxisE8SectionOrbit (golayOctadWord o) ∧
    leechReduction (leechCoordinateFrameLattice 0) ∈ generatedAxisE8FrameClasses S}

/-- Every rooted section is one of the 759 actual coordinate octad sections,
and every one of those sections occurs. -/
theorem generatedAxisE8RootedSections_eq_coordinate_octads (o : Fin 759) :
    generatedAxisE8RootedSections o =
      Set.range (fun t : Fin 759 => generatedAxisE8CoordinateSection (golayOctadWord t)) := by
  ext S
  constructor
  · rintro ⟨⟨g, rfl⟩, hb⟩
    obtain ⟨i, hi⟩ := generatedAxisE8_octad_support_nonempty o
    obtain ⟨p, hp⟩ := generatedAxisE8_rooted_coordinate (golayOctadWord o)
      (golayOctadWord_mem_code o) (golayOctadWord_weight o) i hi g hb
    have hcode : golayPermute p.val (golayOctadWord o) ∈ golayCode :=
      (p.property _).mp (golayOctadWord_mem_code o)
    have hw : ∑ i, ((golayPermute p.val (golayOctadWord o)) i).val = 8 :=
      (Equiv.sum_comp p.val.symm (fun i => (golayOctadWord o i).val)).trans
        (golayOctadWord_weight o)
    obtain ⟨t, ht, _⟩ := golayOctadWord_of_weight_eight _ hcode hw
    exact ⟨t, (congrArg generatedAxisE8CoordinateSection ht).trans hp.symm⟩
  · rintro ⟨t, rfl⟩
    exact generatedAxisE8_coordinate_octad_rooted o t

/-- The actual distinguished-frame section fiber has exactly 759 elements. -/
theorem generatedAxisE8RootedSections_card (o : Fin 759) :
    Nat.card (generatedAxisE8RootedSections o) = 759 := by
  rw [generatedAxisE8RootedSections_eq_coordinate_octads]
  have hi : Function.Injective
      (fun t : Fin 759 => generatedAxisE8CoordinateSection (golayOctadWord t)) :=
    generatedAxisE8CoordinateSection_injective.comp golayOctadWord_injective
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
