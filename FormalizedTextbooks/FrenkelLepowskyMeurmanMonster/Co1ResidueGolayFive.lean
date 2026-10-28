/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadIntersection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOctads

/-! Actual five-point octad incidence for the Golay model of the auxiliary residues. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Each actual five-coordinate set lies in exactly one actual Golay octad. -/
theorem co1ResidueGolay_octad_through_five (S : Finset (Fin 24)) (hS : S.card = 5) :
    ∃! o : Fin 759, S ⊆ golayOctadSupport o := by
  let e := (S.equivFinOfCardEq hS).symm
  let a : Fin 5 → Fin 24 := fun j => (e j).val
  have ha : Function.Injective a := Subtype.val_injective.comp e.injective
  obtain ⟨p, hp⟩ := golayAutomorphism_maps_firstFive a ha
  let c := golayPermute p.val golayStandardOctad
  have hc : c ∈ golayCode := (p.property _).mp golayStandardOctad_mem
  have hw : (∑ i, (c i).val) = 8 :=
    (Equiv.sum_comp p.val.symm (fun i => (golayStandardOctad i).val)).trans
      golayStandardOctad_weight
  obtain ⟨o, ho, _⟩ := golayOctadWord_of_weight_eight c hc hw
  have hso : S ⊆ golayOctadSupport o := by
    intro i hi
    obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
    have hai : a j = i := congrArg Subtype.val hj
    have hpi : p.val.symm i = Fin.castAdd 19 j := by
      rw [← hai, ← hp j, p.val.symm_apply_apply]
    apply (golayOctadWord_ne_zero_iff o i).mp
    rw [ho]
    change golayStandardOctad (p.val.symm i) ≠ 0
    rw [hpi]
    have hjlt : j.val < 8 := lt_trans j.isLt (by decide +kernel)
    simp [golayStandardOctad, hjlt]
  refine ⟨o, hso, ?_⟩
  intro v hvs
  by_contra hvo
  have hsub : S ⊆ golayOctadSupport o ∩ golayOctadSupport v :=
    fun i hi => Finset.mem_inter.mpr ⟨hso hi, hvs hi⟩
  have hcard := Finset.card_le_card hsub
  rw [hS, ← golayOctadIntersection_support] at hcard
  have hle := golayOctad_intersection_le_four o v (fun h => hvo h.symm)
  omega

/-- Every set of at most five actual coordinates is contained in an actual Golay octad. -/
theorem co1ResidueGolay_octad_through_small (S : Finset (Fin 24)) (hS : S.card ≤ 5) :
    ∃ o : Fin 759, S ⊆ golayOctadSupport o := by
  obtain ⟨T, hST, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ S) hS (by decide +kernel : 5 ≤ (Finset.univ : Finset (Fin 24)).card)
  obtain ⟨o, ho, _⟩ := co1ResidueGolay_octad_through_five T hT
  exact ⟨o, hST.trans ho⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
