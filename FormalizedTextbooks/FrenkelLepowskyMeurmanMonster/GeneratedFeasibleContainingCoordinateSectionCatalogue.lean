/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinateSourceGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinateIncidentCodes

/-! The original coordinate E8 sections through the old fixed incident root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Literal supported coordinate sections determine the whole original binary codeword. -/
theorem generatedFeasibleContaining_coordinate_section_injective :
    Function.Injective generatedAxisE8CoordinateSection := by
  intro c d h
  have hm (b : Fin 24 → ZMod 2) (i : Fin 24) :
      leechCoordinateFrameLattice i ∈ generatedAxisE8CoordinateSection b ↔ b i ≠ 0 := by
    constructor
    · intro hu hi
      have hz := hu i hi
      change (if i = i then (8 : ℤ) else 0) = 0 at hz
      norm_num at hz
    · exact generatedAxisE8_frame_supported b i
  funext i
  have hi : c i ≠ 0 ↔ d i ≠ 0 := by
    rw [← hm, ← hm, h]
  have hb : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b := by decide
  exact hb _ _ hi

/-- The catalogue consists of the actual integral coordinate sections of these original codes. -/
def generatedFeasibleContainingCoordinateIncidentSections : Set (Submodule ℤ leechIntegral) :=
  Set.range (fun d : generatedFeasibleContainingCoordinateIncidentCodes =>
    generatedAxisE8CoordinateSection (golayEncoder (golayLabelCoefficients d.val)))

/-- Different original incident codes give different entire integral coordinate sections. -/
theorem generatedFeasibleContainingCoordinateIncidentSections_injective :
    Function.Injective (fun d : generatedFeasibleContainingCoordinateIncidentCodes =>
      generatedAxisE8CoordinateSection (golayEncoder (golayLabelCoefficients d.val))) := by
  intro d e h
  apply Subtype.ext
  apply golayLabelCoefficients_injective
  apply golayEncoder_injective
  exact generatedFeasibleContaining_coordinate_section_injective h

/-- This actual integral section catalogue has exactly 77 members. -/
theorem generatedFeasibleContainingCoordinateIncidentSections_card :
    Nat.card generatedFeasibleContainingCoordinateIncidentSections = 77 := by
  unfold generatedFeasibleContainingCoordinateIncidentSections
  rw [← Nat.card_congr (Equiv.ofInjective _
    generatedFeasibleContainingCoordinateIncidentSections_injective), Nat.card_eq_fintype_card]
  rw [Fintype.card_coe, generatedFeasibleContainingCoordinateIncidentCodes_card]

/-- Original label weight is exactly the weight of its actual encoder word. -/
theorem generatedFeasibleContaining_coordinate_word_weight (d : Fin 4096) :
    (∑ i : Fin 24, (golayEncoder (golayLabelCoefficients d) i).val) =
      golayMaskWeight (golayEncodedMask d.val) := by
  simp_rw [golayLabelEncoder_match]
  rfl

private theorem encoder_bit (d : Fin 4096) (i : Fin 24) :
    golayEncoder (golayLabelCoefficients d) i ≠ 0 ↔
      (golayEncodedMask d.val).testBit i.val = true := by
  rw [golayLabelEncoder_boolean]
  cases hb : (golayEncodedMask d.val).testBit i.val <;> norm_num [golayBooleanCast]

/-- An actual coordinate code section contains the incident root exactly when both root
coordinates lie in its literal binary support. -/
theorem generatedFeasibleContaining_coordinate_root_mem (c : Fin 24 → ZMod 2) :
    Sum.inl (0, generatedFeasibleContainingIncidentPair) ∈
      generatedAxisE8ShortLines (generatedAxisE8CoordinateSection c) ↔
        c 8 ≠ 0 ∧ c 9 ≠ 0 := by
  change generatedOctadSupported c
    (griessShortIntegral (Sum.inl (0, generatedFeasibleContainingIncidentPair))) ↔ _
  constructor
  · intro h
    constructor
    · intro hc
      have hz := h 8 hc
      norm_num [griessShortIntegral, generatedFeasibleContainingIncidentPair_coordinates] at hz
    · intro hc
      have hz := h 9 hc
      norm_num [griessShortIntegral, generatedFeasibleContainingIncidentPair_coordinates] at hz
  · rintro ⟨h8, h9⟩ i hi
    have hn8 : i ≠ 8 := by rintro rfl; exact h8 hi
    have hn9 : i ≠ 9 := by rintro rfl; exact h9 hi
    simp [griessShortIntegral, generatedFeasibleContainingIncidentPair_coordinates, hn8, hn9]

/-- Every actual weight-eight code section through the incident root is in the original catalogue.
-/
theorem generatedFeasibleContainingCoordinateIncidentSections_of_word
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hw : (∑ i : Fin 24, (c i).val) = 8)
    (hr : Sum.inl (0, generatedFeasibleContainingIncidentPair) ∈
      generatedAxisE8ShortLines (generatedAxisE8CoordinateSection c)) :
    generatedAxisE8CoordinateSection c ∈
      generatedFeasibleContainingCoordinateIncidentSections := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨d, hd⟩ := golayLabelCoefficients_bijective.2 t
  have he : golayEncoder (golayLabelCoefficients d) = c := by rwa [hd]
  have hp := (generatedFeasibleContaining_coordinate_root_mem c).mp hr
  have hm : d ∈ generatedFeasibleContainingCoordinateIncidentCodes := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← generatedFeasibleContaining_coordinate_word_weight, he]
      exact hw
    · constructor
      · apply (encoder_bit d 8).mp
        simpa only [he] using hp.1
      · apply (encoder_bit d 9).mp
        simpa only [he] using hp.2
  refine ⟨⟨d, hm⟩, ?_⟩
  change generatedAxisE8CoordinateSection (golayEncoder (golayLabelCoefficients d)) = _
  rw [he]

private theorem octad_permutation_between (b c : Fin 24 → ZMod 2)
    (hb : b ∈ golayCode) (hc : c ∈ golayCode)
    (hwb : (∑ i : Fin 24, (b i).val) = 8)
    (hwc : (∑ i : Fin 24, (c i).val) = 8) :
    ∃ p : golayAutomorphismSubgroup, golayPermute p.val b = c := by
  obtain ⟨p, hp⟩ := golayOctad_to_standard c hc hwc
  obtain ⟨q, hq⟩ := golayOctad_to_standard b hb hwb
  refine ⟨p⁻¹ * q, ?_⟩
  change golayPermute (p.val⁻¹ * q.val) b = c
  rw [golayPermute_mul, hq, ← hp, ← golayPermute_mul]
  rw [inv_mul_cancel, golayPermute_one]

/-- Every actual weight-eight code section belongs to the genuine original E8 section orbit. -/
theorem generatedFeasibleContaining_coordinate_section_mem_orbit
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode)
    (hw : (∑ i : Fin 24, (c i).val) = 8) :
    generatedAxisE8CoordinateSection c ∈
      generatedAxisE8SectionOrbit (golayOctadWord generatedOctadBasisOctad) := by
  obtain ⟨p, hp⟩ := octad_permutation_between
    (golayOctadWord generatedOctadBasisOctad) c (golayOctadWord_mem_code _) hc
      (golayOctadWord_weight _) hw
  refine ⟨golayPermutationIsometry p, ?_⟩
  change generatedAxisE8ImageSection (golayPermutationIsometry p)
    (golayOctadWord generatedOctadBasisOctad) = _
  rw [generatedAxisE8_permutation_image, hp]

/-- The entire literal coordinate catalogue lies in the genuine original rooted section space. -/
theorem generatedFeasibleContainingCoordinateIncidentSections_subset_rooted :
    generatedFeasibleContainingCoordinateIncidentSections ⊆
      generatedFeasibleContainingRootedSections := by
  rintro S ⟨d, rfl⟩
  have hm := Finset.mem_filter.mp d.property
  have hw := (Finset.mem_filter.mp hm.1).2
  constructor
  · apply generatedFeasibleContaining_coordinate_section_mem_orbit
      (golayEncoder (golayLabelCoefficients d.val)) ⟨_, rfl⟩
    rw [generatedFeasibleContaining_coordinate_word_weight]
    exact hw
  · apply (generatedFeasibleContaining_coordinate_root_mem _).mpr
    exact ⟨(encoder_bit d.val 8).mpr hm.2.1, (encoder_bit d.val 9).mpr hm.2.2⟩

/-- These are precisely the 77 original coordinate sections inside the actual rooted section space.
-/
def generatedFeasibleContainingCoordinateIncidentRootedSections :
    Set generatedFeasibleContainingRootedSections :=
  {S | S.val ∈ generatedFeasibleContainingCoordinateIncidentSections}

/-- Restricting the original catalogue to the actual rooted space changes none of its members. -/
def generatedFeasibleContainingCoordinateIncidentRootedSectionsEquiv :
    generatedFeasibleContainingCoordinateIncidentRootedSections ≃
      generatedFeasibleContainingCoordinateIncidentSections where
  toFun S := ⟨S.val.val, S.property⟩
  invFun S := ⟨⟨S.val, generatedFeasibleContainingCoordinateIncidentSections_subset_rooted
    S.property⟩, S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly 77 members of the actual rooted section space are original coordinate sections. -/
theorem generatedFeasibleContainingCoordinateIncidentRootedSections_card :
    Nat.card generatedFeasibleContainingCoordinateIncidentRootedSections = 77 := by
  rw [Nat.card_congr generatedFeasibleContainingCoordinateIncidentRootedSectionsEquiv,
    generatedFeasibleContainingCoordinateIncidentSections_card]

/-- Each original incident code names its genuine entire rooted integral section. -/
def generatedFeasibleContainingCoordinateIncidentCodeSection
    (d : generatedFeasibleContainingCoordinateIncidentCodes) :
    generatedFeasibleContainingRootedSections :=
  ⟨generatedAxisE8CoordinateSection (golayEncoder (golayLabelCoefficients d.val)),
    generatedFeasibleContainingCoordinateIncidentSections_subset_rooted ⟨d, rfl⟩⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
