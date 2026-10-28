/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22HexadRepresentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueGolayFive

/-! The nearby-pair commutation hypothesis of Ivanov II Proposition 4.2.5 holds in every
representation of the actual Golay hexad geometry. Its distant graph remains separate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Two auxiliary M22 pair points share an actual containing-octad hexad. -/
def co1ResidueM22CommonHexad (p q : Fin 24) (s t : Co1ResidueM22Point p q) : Prop :=
  ∃ o : Fin 759, p ∈ golayOctadSupport o ∧ q ∈ golayOctadSupport o ∧
    s.val ⊆ co1ResidueM22Hexad p q o ∧ t.val ⊆ co1ResidueM22Hexad p q o

/-- The source distant pairs are disjoint pair points not contained in any common Golay hexad. -/
def co1ResidueM22Distant (p q : Fin 24) (s t : Co1ResidueM22Point p q) : Prop :=
  Disjoint s.val t.val ∧ ¬ co1ResidueM22CommonHexad p q s t

/-- Overlapping actual pair points belong to a common actual hexad,
by five-point octad incidence. -/
theorem co1ResidueM22_common_hexad_of_overlap (p q : Fin 24)
    (s t : Co1ResidueM22Point p q) (hst : (s.val ∩ t.val).Nonempty) :
    co1ResidueM22CommonHexad p q s t := by
  have hsum := Finset.card_union_add_card_inter s.val t.val
  have hinter : 1 ≤ (s.val ∩ t.val).card := Finset.one_le_card.mpr hst
  rw [s.property.1, t.property.1] at hsum
  have hU : (s.val ∪ t.val).card ≤ 3 := by omega
  let S : Finset (Fin 24) := {p, q} ∪ (s.val ∪ t.val)
  have hcard : S.card ≤ 5 := by
    have h := Finset.card_union_le ({p, q} : Finset (Fin 24)) (s.val ∪ t.val)
    have hpq : ({p, q} : Finset (Fin 24)).card ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le p ({q} : Finset (Fin 24))
    dsimp only [S]
    omega
  obtain ⟨o, ho⟩ := co1ResidueGolay_octad_through_small S hcard
  have hss : s.val ⊆ golayOctadSupport o :=
    fun i hi => ho (Finset.mem_union_right _ (Finset.mem_union_left _ hi))
  have htt : t.val ⊆ golayOctadSupport o :=
    fun i hi => ho (Finset.mem_union_right _ (Finset.mem_union_right _ hi))
  refine ⟨o, ho (by simp [S]), ho (by simp [S]), ?_, ?_⟩
  · intro i hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hss hi⟩⟩
    · intro h
      exact s.property.2.2 (h ▸ hi)
    · intro h
      exact s.property.2.1 (h ▸ hi)
  · intro i hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, htt hi⟩⟩
    · intro h
      exact t.property.2.2 (h ▸ hi)
    · intro h
      exact t.property.2.1 (h ▸ hi)

/-- Every nearby pair in the source auxiliary M22 graph lies in a genuine Golay hexad. -/
theorem co1ResidueM22_common_hexad_of_not_distant (p q : Fin 24)
    (s t : Co1ResidueM22Point p q) (h : ¬ co1ResidueM22Distant p q s t) :
    co1ResidueM22CommonHexad p q s t := by
  by_cases hd : Disjoint s.val t.val
  · by_contra hn
    exact h ⟨hd, hn⟩
  · exact co1ResidueM22_common_hexad_of_overlap p q s t
      (Finset.not_disjoint_iff_nonempty_inter.mp hd)

/-- The source nearby-commutation assumption follows from the actual hexad relations;
it is not separately assumed about the representation. -/
theorem co1ResidueM22_nearby_commute {G : Type*} [Group G] (p q : Fin 24)
    (hpq : p ≠ q) (phi : Co1ResidueM22Point p q → G)
    (hsquare : ∀ s, phi s * phi s = 1)
    (hline : ∀ a b c, co1ResidueM22Line p q a b c → phi a * phi b * phi c = 1)
    (s t : Co1ResidueM22Point p q) (h : ¬ co1ResidueM22Distant p q s t) :
    Commute (phi s) (phi t) := by
  obtain ⟨o, hp, hq, hs, ht⟩ := co1ResidueM22_common_hexad_of_not_distant p q s t h
  exact co1ResidueM22_hexad_commute p q hpq o hp hq phi hsquare hline s t hs ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
