/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Code.Walls.rc3_minimalwitnessencoded

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace














inductive WitnessClass where
  
  | neither : WitnessClass
  
  | onlyK : WitnessClass
  
  | onlyL : WitnessClass
  
  | both : WitnessClass
  deriving DecidableEq, Fintype, Repr

namespace WitnessClass

instance : Inhabited WitnessClass := ⟨neither⟩

end WitnessClass

open WitnessClass

variable {α : Type*}




noncomputable def rc6_classify (K L : Set α) (i : α) : WitnessClass := by
  classical
  exact
    if i ∈ K then (if i ∈ L then both else onlyK)
    else (if i ∈ L then onlyL else neither)




theorem rc6_classify_eq_both {K L : Set α} (i : α) :
    rc6_classify K L i = both ↔ i ∈ K ∧ i ∈ L := by
  classical
  unfold rc6_classify
  split_ifs with hK hL <;> simp_all


theorem rc6_classify_eq_onlyK {K L : Set α} (i : α) :
    rc6_classify K L i = onlyK ↔ i ∈ K ∧ i ∉ L := by
  classical
  unfold rc6_classify
  split_ifs with hK hL <;> simp_all


theorem rc6_classify_eq_onlyL {K L : Set α} (i : α) :
    rc6_classify K L i = onlyL ↔ i ∉ K ∧ i ∈ L := by
  classical
  unfold rc6_classify
  split_ifs with hK hL <;> simp_all


theorem rc6_classify_eq_neither {K L : Set α} (i : α) :
    rc6_classify K L i = neither ↔ i ∉ K ∧ i ∉ L := by
  classical
  unfold rc6_classify
  split_ifs with hK hL <;> simp_all









theorem rc6_classify_ne_both_of_disjoint {K L : Set α} (h : Disjoint K L) (i : α) :
    rc6_classify K L i ≠ both := by
  intro hcl
  obtain ⟨hK, hL⟩ := (rc6_classify_eq_both i).mp hcl
  exact Set.disjoint_left.mp h hK hL




theorem rc6_classify_mem_three_of_disjoint {K L : Set α} (h : Disjoint K L) (i : α) :
    rc6_classify K L i ∈ ({neither, onlyK, onlyL} : Finset WitnessClass) := by
  have hne : rc6_classify K L i ≠ both := rc6_classify_ne_both_of_disjoint h i
  cases hcl : rc6_classify K L i <;> simp_all




theorem rc6_overlap_trichotomy {K L : Set α} (h : Disjoint K L) (i : α) :
    (i ∈ K ∧ i ∉ L) ∨ (i ∉ K ∧ i ∈ L) ∨ (i ∉ K ∧ i ∉ L) := by
  classical
  by_cases hK : i ∈ K
  · exact Or.inl ⟨hK, fun hL => Set.disjoint_left.mp h hK hL⟩
  · by_cases hL : i ∈ L
    · exact Or.inr (Or.inl ⟨hK, hL⟩)
    · exact Or.inr (Or.inr ⟨hK, hL⟩)









section Finset

variable [DecidableEq α]




theorem rc6_base_eq_three_pieces (s K L : Finset α) :
    s = (s ∩ K) ∪ (s ∩ L) ∪ (s \ (K ∪ L)) := by
  ext a
  simp only [mem_union, mem_inter, mem_sdiff, Finset.mem_union]
  constructor
  · intro ha
    by_cases hK : a ∈ K
    · exact Or.inl (Or.inl ⟨ha, hK⟩)
    · by_cases hL : a ∈ L
      · exact Or.inl (Or.inr ⟨ha, hL⟩)
      · exact Or.inr ⟨ha, fun h => h.elim hK hL⟩
  · rintro ((⟨ha, _⟩ | ⟨ha, _⟩) | ⟨ha, _⟩) <;> exact ha


theorem rc6_onlyK_disjoint_onlyL {K L : Finset α} (h : Disjoint K L) (s : Finset α) :
    Disjoint (s ∩ K) (s ∩ L) :=
  h.mono inter_subset_right inter_subset_right


theorem rc6_KorL_disjoint_neither (K L : Finset α) (s : Finset α) :
    Disjoint ((s ∩ K) ∪ (s ∩ L)) (s \ (K ∪ L)) := by
  rw [disjoint_left]
  intro a ha hb
  simp only [mem_union, mem_inter, mem_sdiff, Finset.mem_union] at ha hb
  rcases ha with ⟨_, hK⟩ | ⟨_, hL⟩
  · exact hb.2 (Or.inl hK)
  · exact hb.2 (Or.inr hL)





theorem rc6_card_base_eq_three_pieces {K L : Finset α} (h : Disjoint K L) (s : Finset α) :
    #s = #(s ∩ K) + #(s ∩ L) + #(s \ (K ∪ L)) := by
  conv_lhs => rw [rc6_base_eq_three_pieces s K L]
  rw [card_union_of_disjoint (rc6_KorL_disjoint_neither K L s),
    card_union_of_disjoint (rc6_onlyK_disjoint_onlyL h s)]

end Finset










section UseSite

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {A B : Set (ConfigSpace α)} {ω : ConfigSpace α} {s K L : Finset α}




theorem rc6_witness_diagonal_empty (hw : SupportEncodedMinimalWitness A B ω s K L) (i : α) :
    ¬ (i ∈ K ∧ i ∈ L) := by
  rintro ⟨hK, hL⟩
  exact Finset.disjoint_left.mp hw.disjoint hK hL




theorem rc6_witness_overlap_trichotomy (hw : SupportEncodedMinimalWitness A B ω s K L) (i : α) :
    (i ∈ K ∧ i ∉ L) ∨ (i ∉ K ∧ i ∈ L) ∨ (i ∉ K ∧ i ∉ L) := by
  have h : Disjoint (K : Set α) (L : Set α) := by
    rw [Finset.disjoint_coe]; exact hw.disjoint
  simpa only [Finset.mem_coe] using rc6_overlap_trichotomy h i





theorem rc6_witness_card_split (hw : SupportEncodedMinimalWitness A B ω s K L) :
    #s = #(s ∩ K) + #(s ∩ L) + #(s \ (K ∪ L)) :=
  rc6_card_base_eq_three_pieces hw.disjoint s

end UseSite







section Nonvacuity

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {A B : Set (ConfigSpace α)} {ω : ConfigSpace α}




theorem rc6_exists_witness_split (hω : ω ∈ disjointOccurrence A B) :
    ∃ s K L : Finset α, SupportEncodedMinimalWitness A B ω s K L
      ∧ ∀ i : α, ¬ (i ∈ K ∧ i ∈ L) := by
  obtain ⟨s, K, L, hw⟩ := exists_supportEncodedMinimalWitness hω
  exact ⟨s, K, L, hw, fun i => rc6_witness_diagonal_empty hw i⟩

end Nonvacuity

















theorem rc6_overlap_split {K L : Set α} (h : Disjoint K L) (i : α) :
    rc6_classify K L i ≠ both
      ∧ rc6_classify K L i ∈ ({neither, onlyK, onlyL} : Finset WitnessClass)
      ∧ ((i ∈ K ∧ i ∉ L) ∨ (i ∉ K ∧ i ∈ L) ∨ (i ∉ K ∧ i ∉ L)) :=
  ⟨rc6_classify_ne_both_of_disjoint h i, rc6_classify_mem_three_of_disjoint h i,
    rc6_overlap_trichotomy h i⟩

end StatMech.Walls
