/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FiniteConnected
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismTransitivity

/-! Genuine Golay automorphisms fixing the two distinguished coordinates preserve
auxiliary pair points, original hexad lines, and the actual distant relation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The pair-point action of an actual Golay automorphism fixing both distinguished positions. -/
def co1ResidueM22PointMap (g : golayAutomorphismSubgroup)
    (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) (s : Co1ResidueM22Point 0 1) :
    Co1ResidueM22Point 0 1 :=
  ⟨s.val.image g.val, by
    refine ⟨(Finset.card_image_of_injective _ g.val.injective).trans s.property.1, ?_, ?_⟩
    · rintro h
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
      exact s.property.2.1 (g.val.injective (he.trans h0.symm) ▸ hi)
    · rintro h
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
      exact s.property.2.2 (g.val.injective (he.trans h1.symm) ▸ hi)⟩

/-- An actual Golay automorphism carries every actual octad support to an actual octad support. -/
theorem co1ResidueM22_octad_image (g : golayAutomorphismSubgroup) (o : Fin 759) :
    ∃ v : Fin 759, golayOctadSupport v = (golayOctadSupport o).image g.val := by
  let c := golayPermute g.val (golayOctadWord o)
  have hc : c ∈ golayCode := (g.property _).mp (golayOctadWord_mem_code o)
  have hw : ∑ i, (c i).val = 8 :=
    (Equiv.sum_comp g.val.symm (fun i => (golayOctadWord o i).val)).trans
      (golayOctadWord_weight o)
  obtain ⟨v, hv, _⟩ := golayOctadWord_of_weight_eight c hc hw
  refine ⟨v, ?_⟩
  ext k
  rw [← golayOctadWord_ne_zero_iff, hv]
  change golayOctadWord o (g.val.symm k) ≠ 0 ↔ _
  rw [golayOctadWord_ne_zero_iff]
  constructor
  · intro hk
    exact Finset.mem_image.mpr ⟨g.val.symm k, hk, g.val.apply_symm_apply k⟩
  · rintro hk
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hk
    rwa [← he, g.val.symm_apply_apply]

/-- Original containing-hexad incidence is preserved by the genuine point action. -/
theorem co1ResidueM22_common_hexad_map (g : golayAutomorphismSubgroup)
    (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) (s t : Co1ResidueM22Point 0 1)
    (h : co1ResidueM22CommonHexad 0 1 s t) :
    co1ResidueM22CommonHexad 0 1 (co1ResidueM22PointMap g h0 h1 s)
      (co1ResidueM22PointMap g h0 h1 t) := by
  obtain ⟨o, ho0, ho1, hs, ht⟩ := h
  obtain ⟨v, hv⟩ := co1ResidueM22_octad_image g o
  have hh : co1ResidueM22Hexad 0 1 v = (co1ResidueM22Hexad 0 1 o).image g.val := by
    rw [co1ResidueM22Hexad, co1ResidueM22Hexad, hv,
      Finset.image_erase g.val.injective, Finset.image_erase g.val.injective, h0, h1]
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · rw [hv]
    exact h0 ▸ Finset.mem_image.mpr ⟨0, ho0, rfl⟩
  · rw [hv]
    exact h1 ▸ Finset.mem_image.mpr ⟨1, ho1, rfl⟩
  · rw [hh]
    exact Finset.image_subset_image hs
  · rw [hh]
    exact Finset.image_subset_image ht

/-- Original three-pair hexad lines are preserved by actual Golay automorphisms. -/
theorem co1ResidueM22_line_map (g : golayAutomorphismSubgroup)
    (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) (s t u : Co1ResidueM22Point 0 1)
    (h : co1ResidueM22Line 0 1 s t u) :
    co1ResidueM22Line 0 1 (co1ResidueM22PointMap g h0 h1 s)
      (co1ResidueM22PointMap g h0 h1 t) (co1ResidueM22PointMap g h0 h1 u) := by
  obtain ⟨o, ho0, ho1, he⟩ := h
  obtain ⟨v, hv⟩ := co1ResidueM22_octad_image g o
  have hh : co1ResidueM22Hexad 0 1 v = (co1ResidueM22Hexad 0 1 o).image g.val := by
    rw [co1ResidueM22Hexad, co1ResidueM22Hexad, hv,
      Finset.image_erase g.val.injective, Finset.image_erase g.val.injective, h0, h1]
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [hv]
    exact h0 ▸ Finset.mem_image.mpr ⟨0, ho0, rfl⟩
  · rw [hv]
    exact h1 ▸ Finset.mem_image.mpr ⟨1, ho1, rfl⟩
  · change s.val.image g.val ∪ t.val.image g.val ∪ u.val.image g.val = _
    rw [← Finset.image_union, ← Finset.image_union, he, hh]

/-- Applying a genuine point action and its inverse recovers the original point. -/
theorem co1ResidueM22PointMap_inverse (g : golayAutomorphismSubgroup)
    (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) (s : Co1ResidueM22Point 0 1) :
    co1ResidueM22PointMap g⁻¹ (by change g.val.symm 0 = 0; exact g.val.symm_apply_eq.mpr h0.symm)
      (by change g.val.symm 1 = 1; exact g.val.symm_apply_eq.mpr h1.symm)
      (co1ResidueM22PointMap g h0 h1 s) = s := by
  apply Subtype.ext
  change (s.val.image g.val).image g.val.symm = s.val
  simp only [Finset.image_image, Function.comp_def, g.val.symm_apply_apply]
  exact Finset.image_id


/-- The genuine point action reflects containing-hexad incidence as well as preserving it. -/
theorem co1ResidueM22_common_hexad_map_iff (g : golayAutomorphismSubgroup)
    (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) (s t : Co1ResidueM22Point 0 1) :
    co1ResidueM22CommonHexad 0 1 (co1ResidueM22PointMap g h0 h1 s)
      (co1ResidueM22PointMap g h0 h1 t) ↔ co1ResidueM22CommonHexad 0 1 s t := by
  constructor
  · intro h
    have hb := co1ResidueM22_common_hexad_map g⁻¹
      (by exact g.val.symm_apply_eq.mpr h0.symm)
      (by exact g.val.symm_apply_eq.mpr h1.symm) _ _ h
    rwa [co1ResidueM22PointMap_inverse, co1ResidueM22PointMap_inverse] at hb
  · exact co1ResidueM22_common_hexad_map g h0 h1 s t

/-- Genuine Golay point actions preserve and reflect the source distant relation. -/
theorem co1ResidueM22_distant_map_iff (g : golayAutomorphismSubgroup)
    (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) (s t : Co1ResidueM22Point 0 1) :
    co1ResidueM22Distant 0 1 (co1ResidueM22PointMap g h0 h1 s)
      (co1ResidueM22PointMap g h0 h1 t) ↔ co1ResidueM22Distant 0 1 s t := by
  rw [co1ResidueM22Distant, co1ResidueM22Distant, co1ResidueM22_common_hexad_map_iff]
  have hd : Disjoint (s.val.image g.val) (t.val.image g.val) ↔ Disjoint s.val t.val := by
    rw [Finset.disjoint_left, Finset.disjoint_left]
    constructor
    · intro h i hi ht
      exact h (Finset.mem_image.mpr ⟨i, hi, rfl⟩) (Finset.mem_image.mpr ⟨i, ht, rfl⟩)
    · intro h k hs ht
      obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hs
      obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp ht
      exact h hi (g.val.injective (hjk.trans hik.symm) ▸ hj)
  exact and_congr_left (fun _ => hd)

/-- Every actual pair-point has a preimage under a genuine Golay point action. -/
theorem co1ResidueM22PointMap_surjective (g : golayAutomorphismSubgroup)
    (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) :
    Function.Surjective (co1ResidueM22PointMap g h0 h1) := by
  intro s
  let hi0 : (g⁻¹).val 0 = 0 := g.val.symm_apply_eq.mpr h0.symm
  let hi1 : (g⁻¹).val 1 = 1 := g.val.symm_apply_eq.mpr h1.symm
  refine ⟨co1ResidueM22PointMap g⁻¹ hi0 hi1 s, ?_⟩
  simpa only [inv_inv] using co1ResidueM22PointMap_inverse g⁻¹ hi0 hi1 s

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
