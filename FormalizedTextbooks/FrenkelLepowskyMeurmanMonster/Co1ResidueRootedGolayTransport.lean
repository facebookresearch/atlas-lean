/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22Automorphisms

/-! Genuine Golay transport between arbitrary distinguished pairs and triple coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem fresh_coordinate (S : Finset (Fin 24)) (hS : S.card ≤ 4) :
    ∃ i : Fin 24, i ∉ S := by
  by_contra hn
  push Not at hn
  have h := Finset.card_le_card (show (Finset.univ : Finset (Fin 24)) ⊆ S from fun i _ => hn i)
  have hu : (Finset.univ : Finset (Fin 24)).card = 24 := by decide +kernel
  rw [hu] at h
  omega

/-- Any ordered three distinct physical coordinates are reached by an actual Golay automorphism. -/
theorem co1ResidueGolay_triple_reach (p q r : Fin 24)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ g : golayAutomorphismSubgroup, g.val 0 = p ∧ g.val 1 = q ∧ g.val 2 = r := by
  obtain ⟨a, ha⟩ := fresh_coordinate ({p, q, r} : Finset (Fin 24)) (by
    have h1 := Finset.card_insert_le p ({q, r} : Finset (Fin 24))
    have h2 := Finset.card_insert_le q ({r} : Finset (Fin 24))
    simp only [Finset.card_singleton] at h2
    omega)
  have hap : a ≠ p := by intro h; exact ha (by simp [h])
  have haq : a ≠ q := by intro h; exact ha (by simp [h])
  have har : a ≠ r := by intro h; exact ha (by simp [h])
  obtain ⟨b, hb⟩ := fresh_coordinate ({p, q, r, a} : Finset (Fin 24)) (by
    have h1 := Finset.card_insert_le p ({q, r, a} : Finset (Fin 24))
    have h2 := Finset.card_insert_le q ({r, a} : Finset (Fin 24))
    have h3 := Finset.card_insert_le r ({a} : Finset (Fin 24))
    simp only [Finset.card_singleton] at h3
    omega)
  have hbp : b ≠ p := by intro h; exact hb (by simp [h])
  have hbq : b ≠ q := by intro h; exact hb (by simp [h])
  have hbr : b ≠ r := by intro h; exact hb (by simp [h])
  have hba : b ≠ a := by intro h; exact hb (by simp [h])
  let t : Fin 5 → Fin 24 := ![p, q, r, a, b]
  have ht : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t]
  obtain ⟨g, hg⟩ := golayAutomorphism_maps_firstFive t ht
  exact ⟨g, hg 0, hg 1, hg 2⟩

/-- Any ordered pair of distinct physical coordinates is reached by an actual Golay automorphism. -/
theorem co1ResidueGolay_pair_reach (p q : Fin 24) (hpq : p ≠ q) :
    ∃ g : golayAutomorphismSubgroup, g.val 0 = p ∧ g.val 1 = q := by
  obtain ⟨r, hr⟩ := fresh_coordinate ({p, q} : Finset (Fin 24)) (by
    have h := Finset.card_insert_le p ({q} : Finset (Fin 24))
    simp only [Finset.card_singleton] at h
    omega)
  have hpr : p ≠ r := by intro h; exact hr (by simp [← h])
  have hqr : q ≠ r := by intro h; exact hr (by simp [← h])
  obtain ⟨g, hp, hq, _⟩ := co1ResidueGolay_triple_reach p q r hpq hpr hqr
  exact ⟨g, hp, hq⟩

/-- A genuine Golay automorphism transports actual pair points between distinguished pairs. -/
def co1ResidueM22RootTransport (g : golayAutomorphismSubgroup)
    {p q p' q' : Fin 24} (hp : g.val p = p') (hq : g.val q = q')
    (s : Co1ResidueM22Point p q) : Co1ResidueM22Point p' q' :=
  ⟨s.val.image g.val, by
    refine ⟨(Finset.card_image_of_injective _ g.val.injective).trans s.property.1, ?_, ?_⟩
    · rintro h
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
      exact s.property.2.1 (g.val.injective (he.trans hp.symm) ▸ hi)
    · rintro h
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
      exact s.property.2.2 (g.val.injective (he.trans hq.symm) ▸ hi)⟩

/-- Root transport preserves the original genuine hexad matching line predicate. -/
theorem co1ResidueM22RootTransport_line (g : golayAutomorphismSubgroup)
    {p q p' q' : Fin 24} (hp : g.val p = p') (hq : g.val q = q')
    (s t u : Co1ResidueM22Point p q) (h : co1ResidueM22Line p q s t u) :
    co1ResidueM22Line p' q' (co1ResidueM22RootTransport g hp hq s)
      (co1ResidueM22RootTransport g hp hq t) (co1ResidueM22RootTransport g hp hq u) := by
  obtain ⟨o, hop, hoq, he⟩ := h
  obtain ⟨v, hv⟩ := co1ResidueM22_octad_image g o
  have hh : co1ResidueM22Hexad p' q' v = (co1ResidueM22Hexad p q o).image g.val := by
    rw [co1ResidueM22Hexad, co1ResidueM22Hexad, hv,
      Finset.image_erase g.val.injective, Finset.image_erase g.val.injective, hp, hq]
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [hv]
    exact hp ▸ Finset.mem_image.mpr ⟨p, hop, rfl⟩
  · rw [hv]
    exact hq ▸ Finset.mem_image.mpr ⟨q, hoq, rfl⟩
  · change s.val.image g.val ∪ t.val.image g.val ∪ u.val.image g.val = _
    rw [← Finset.image_union, ← Finset.image_union, he, hh]

/-- Every actual pair point has a preimage under root transport. -/
theorem co1ResidueM22RootTransport_surjective (g : golayAutomorphismSubgroup)
    {p q p' q' : Fin 24} (hp : g.val p = p') (hq : g.val q = q') :
    Function.Surjective (co1ResidueM22RootTransport g hp hq) := by
  intro s
  let hip : (g⁻¹).val p' = p := g.val.symm_apply_eq.mpr hp.symm
  let hiq : (g⁻¹).val q' = q := g.val.symm_apply_eq.mpr hq.symm
  refine ⟨co1ResidueM22RootTransport g⁻¹ hip hiq s, Subtype.ext ?_⟩
  change (s.val.image g.val.symm).image g.val = s.val
  simp only [Finset.image_image, Function.comp_def, g.val.apply_symm_apply]
  exact Finset.image_id

/-- Root transport exactly preserves physical containment of a third coordinate. -/
theorem co1ResidueM22RootTransport_mem (g : golayAutomorphismSubgroup)
    {p q p' q' : Fin 24} (hp : g.val p = p') (hq : g.val q = q')
    (s : Co1ResidueM22Point p q) (r : Fin 24) :
    g.val r ∈ (co1ResidueM22RootTransport g hp hq s).val ↔ r ∈ s.val := by
  change g.val r ∈ s.val.image g.val ↔ r ∈ s.val
  constructor
  · rintro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    exact g.val.injective he ▸ hi
  · intro h
    exact Finset.mem_image.mpr ⟨r, h, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
