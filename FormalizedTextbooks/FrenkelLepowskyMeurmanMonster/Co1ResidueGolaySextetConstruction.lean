/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueGolayFive

/-! Genuine Golay sextets constructed from an actual four-coordinate tetrad. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual octads containing a given physical tetrad. -/
def co1ResidueGolayTetradOctads (T : Finset (Fin 24)) : Finset (Fin 759) :=
  Finset.univ.filter (fun o => T ⊆ golayOctadSupport o)

/-- The physical tetrad and the complementary tetrads of all octads through it. -/
def co1ResidueGolaySextetBlocks (T : Finset (Fin 24)) : Finset (Finset (Fin 24)) :=
  insert T ((co1ResidueGolayTetradOctads T).image (fun o => golayOctadSupport o \ T))

/-- Membership records either the original tetrad or an actual octad complement. -/
theorem co1ResidueGolaySextetBlocks_mem (T B : Finset (Fin 24)) :
    B ∈ co1ResidueGolaySextetBlocks T ↔
      B = T ∨ ∃ o : Fin 759, T ⊆ golayOctadSupport o ∧ B = golayOctadSupport o \ T := by
  simp only [co1ResidueGolaySextetBlocks, Finset.mem_insert, Finset.mem_image,
    co1ResidueGolayTetradOctads, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim Or.inl (fun ⟨o, ho, he⟩ => Or.inr ⟨o, ho, he.symm⟩),
    fun h => h.elim Or.inl (fun ⟨o, ho, he⟩ => Or.inr ⟨o, ho, he.symm⟩)⟩

private theorem intersection_eq (T : Finset (Fin 24)) (hT : T.card = 4)
    (o p : Fin 759) (ho : T ⊆ golayOctadSupport o) (hp : T ⊆ golayOctadSupport p)
    (hop : o ≠ p) : golayOctadSupport o ∩ golayOctadSupport p = T := by
  have hsub : T ⊆ golayOctadSupport o ∩ golayOctadSupport p :=
    fun i hi => Finset.mem_inter.mpr ⟨ho hi, hp hi⟩
  have hle := golayOctad_intersection_le_four o p hop
  rw [golayOctadIntersection_support] at hle
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- Every member of the constructed system has exactly four actual coordinates. -/
theorem co1ResidueGolaySextetBlocks_tetrad (T : Finset (Fin 24)) (hT : T.card = 4)
    (B : Finset (Fin 24)) (hB : B ∈ co1ResidueGolaySextetBlocks T) : B.card = 4 := by
  rcases (co1ResidueGolaySextetBlocks_mem T B).mp hB with rfl | ⟨o, ho, rfl⟩
  · exact hT
  · rw [Finset.card_sdiff_of_subset ho, golayOctadSupport_card, hT]

/-- Distinct members are disjoint physical tetrads, by the actual octad intersection bound. -/
theorem co1ResidueGolaySextetBlocks_disjoint (T : Finset (Fin 24)) (hT : T.card = 4) :
    (co1ResidueGolaySextetBlocks T : Set (Finset (Fin 24))).PairwiseDisjoint id := by
  intro B hB C hC hBC
  rcases (co1ResidueGolaySextetBlocks_mem T B).mp hB with hBT | ⟨o, ho, rfl⟩
  · subst B
    rcases (co1ResidueGolaySextetBlocks_mem T C).mp hC with hCT | ⟨p, hp, rfl⟩
    · exact False.elim (hBC hCT.symm)
    · exact Finset.disjoint_sdiff
  · rcases (co1ResidueGolaySextetBlocks_mem T C).mp hC with hCT | ⟨p, hp, rfl⟩
    · subst C
      exact Finset.sdiff_disjoint
    · apply Finset.disjoint_left.mpr
      intro i hi hj
      have hop : o ≠ p := fun h => hBC (congrArg (fun q => golayOctadSupport q \ T) h)
      have hint := intersection_eq T hT o p ho hp hop
      have him : i ∈ T := by
        rw [← hint]
        exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hj).1⟩
      exact (Finset.mem_sdiff.mp hi).2 him

/-- The constructed disjoint tetrads cover all twenty-four actual coordinates. -/
theorem co1ResidueGolaySextetBlocks_point (T : Finset (Fin 24)) (hT : T.card = 4)
    (i : Fin 24) : ∃ B ∈ co1ResidueGolaySextetBlocks T, i ∈ B := by
  by_cases hi : i ∈ T
  · exact ⟨T, Finset.mem_insert_self _ _, hi⟩
  · obtain ⟨o, ho, _⟩ := co1ResidueGolay_octad_through_five (insert i T)
      (by rw [Finset.card_insert_of_notMem hi, hT])
    have hTo : T ⊆ golayOctadSupport o := (Finset.subset_insert _ _).trans ho
    refine ⟨golayOctadSupport o \ T, ?_, ?_⟩
    · exact (co1ResidueGolaySextetBlocks_mem _ _).mpr (Or.inr ⟨o, hTo, rfl⟩)
    · exact Finset.mem_sdiff.mpr ⟨ho (Finset.mem_insert_self _ _), hi⟩

private theorem blocks_cover {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset (Finset α)) (hS : ∀ i : α, ∃ B ∈ S, i ∈ B) :
    S.biUnion id = Finset.univ := by
  ext i
  obtain ⟨B, hB, hi⟩ := hS i
  exact iff_of_true (Finset.mem_biUnion.mpr ⟨B, hB, hi⟩) (Finset.mem_univ i)

/-- The constructed physical tetrads cover the complete coordinate set. -/
theorem co1ResidueGolaySextetBlocks_cover (T : Finset (Fin 24)) (hT : T.card = 4) :
    (co1ResidueGolaySextetBlocks T).biUnion id = Finset.univ := by
  exact blocks_cover _ (co1ResidueGolaySextetBlocks_point T hT)

/-- A genuine sextet has precisely six blocks, derived from its disjoint cover. -/
theorem co1ResidueGolaySextetBlocks_card (T : Finset (Fin 24)) (hT : T.card = 4) :
    (co1ResidueGolaySextetBlocks T).card = 6 := by
  have hc := Finset.card_biUnion (co1ResidueGolaySextetBlocks_disjoint T hT)
  rw [co1ResidueGolaySextetBlocks_cover T hT, Finset.card_univ, Fintype.card_fin] at hc
  have hs : (∑ B ∈ co1ResidueGolaySextetBlocks T, B.card) =
      (co1ResidueGolaySextetBlocks T).card * 4 := by
    calc
      _ = ∑ _B ∈ co1ResidueGolaySextetBlocks T, 4 :=
        Finset.sum_congr rfl (fun B hB => co1ResidueGolaySextetBlocks_tetrad T hT B hB)
      _ = _ := by simp
  dsimp only [id_eq] at hc
  rw [hs] at hc
  omega

private theorem complementary_union {α : Type*} [DecidableEq α]
    (T O P : Finset α) (h : O ∩ P = T) :
    (O \ T) ∪ (P \ T) = symmDiff O P := by
  ext i
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_symmDiff]
  have hi : i ∈ T ↔ i ∈ O ∧ i ∈ P := by rw [← h, Finset.mem_inter]
  tauto

/-- Each pair of distinct tetrads in the construction unites to a genuine Golay octad. -/
theorem co1ResidueGolaySextetBlocks_octad (T : Finset (Fin 24)) (hT : T.card = 4)
    (B C : Finset (Fin 24)) (hB : B ∈ co1ResidueGolaySextetBlocks T)
    (hC : C ∈ co1ResidueGolaySextetBlocks T) (hBC : B ≠ C) :
    ∃ o : Fin 759, B ∪ C = golayOctadSupport o := by
  rcases (co1ResidueGolaySextetBlocks_mem T B).mp hB with hBT | ⟨o, ho, rfl⟩
  · subst B
    rcases (co1ResidueGolaySextetBlocks_mem T C).mp hC with hCT | ⟨p, hp, rfl⟩
    · exact False.elim (hBC hCT.symm)
    · exact ⟨p, Finset.union_sdiff_of_subset hp⟩
  · rcases (co1ResidueGolaySextetBlocks_mem T C).mp hC with hCT | ⟨p, hp, rfl⟩
    · subst C
      exact ⟨o, by rw [Finset.union_comm]; exact Finset.union_sdiff_of_subset ho⟩
    · have hop : o ≠ p := fun h => hBC (congrArg (fun q => golayOctadSupport q \ T) h)
      have hint := intersection_eq T hT o p ho hp hop
      obtain ⟨u, hu, _⟩ := golayOctad_sum_octad o p
        (by rw [golayOctadIntersection_support, hint, hT])
      refine ⟨u, ?_⟩
      rw [golayOctad_sum_support o p u hu]
      exact complementary_union T _ _ hint

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
