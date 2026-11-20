/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Code.Walls.rc70butterflymeasure

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}







def rc71_resolveMember (i : Fin n) (U : Finset (Fin n ⊕ Fin n)) : Finset (Fin n ⊕ Fin n) :=
  if Sum.inl i ∈ U ∧ Sum.inr i ∈ U then U.erase (Sum.inr i) else U



noncomputable def rc71_resolveLeft (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    Finset (Finset (Fin n ⊕ Fin n)) :=
  Fam.image (rc71_resolveMember i)





noncomputable def rc71_disjPreservingCompress (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    Finset (Finset (Fin n ⊕ Fin n)) :=
  rc71_resolveLeft i (StatMech.doubleCompress i Fam)










theorem rc71_resolveMember_not_both (i : Fin n) (U : Finset (Fin n ⊕ Fin n)) :
    ¬ (Sum.inl i ∈ rc71_resolveMember i U ∧ Sum.inr i ∈ rc71_resolveMember i U) := by
  unfold rc71_resolveMember
  split_ifs with h
  · rintro ⟨_, hr⟩
    exact (Finset.notMem_erase _ _) hr
  · rintro ⟨hl, hr⟩
    exact h ⟨hl, hr⟩




theorem rc71_resolveLeft_disjPreserving_at (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    ∀ V ∈ rc71_resolveLeft i Fam, ¬ (Sum.inl i ∈ V ∧ Sum.inr i ∈ V) := by
  intro V hV
  rw [rc71_resolveLeft, Finset.mem_image] at hV
  obtain ⟨U, _, rfl⟩ := hV
  exact rc71_resolveMember_not_both i U










set_option maxRecDepth 4000 in





theorem rc71_witness_disjPreserving :
    rc70_DisjPreserving 2
      (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})) := by
  decide

set_option maxRecDepth 4000 in





theorem rc71_witness_card_preserved :
    (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})).card
      = (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}).card := by
  decide










open Classical in




def rc71_IsBoxDoubled (Fam : Finset (Finset (Fin n ⊕ Fin n))) : Prop :=
  ∃ 𝒜' ℬ' : Finset (Finset (Fin n)), StatMech.boxDoubled 𝒜' ℬ' = Fam

set_option maxRecDepth 4000 in




theorem rc71_witness_compressed_eq :
    rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})
      = ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2))) := by
  decide


theorem rc71_dbl_left : StatMech.dbl ({0} : Finset (Fin 2)) ∅ = ({Sum.inl 0} : Finset (Fin 2 ⊕ Fin 2)) := by
  decide


theorem rc71_dbl_right : StatMech.dbl (∅ : Finset (Fin 2)) {0} = ({Sum.inr 0} : Finset (Fin 2 ⊕ Fin 2)) := by
  decide


theorem rc71_dbl_empty : StatMech.dbl (∅ : Finset (Fin 2)) ∅ = (∅ : Finset (Fin 2 ⊕ Fin 2)) := by
  decide



theorem rc71_empty_notMem : (∅ : Finset (Fin 2 ⊕ Fin 2)) ∉ ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2))) := by
  decide

open Classical in














theorem rc71_disjPreserving_not_boxDoubled :
    rc70_DisjPreserving 2 ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2)))
    ∧ ¬ rc71_IsBoxDoubled ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2))) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨𝒜', ℬ', hEq⟩
  
  have hL : ({Sum.inl 0} : Finset (Fin 2 ⊕ Fin 2)) ∈ StatMech.boxDoubled 𝒜' ℬ' := by
    rw [hEq]; decide
  have hR : ({Sum.inr 0} : Finset (Fin 2 ⊕ Fin 2)) ∈ StatMech.boxDoubled 𝒜' ℬ' := by
    rw [hEq]; decide
  
  rw [StatMech.mem_boxDoubled] at hL
  obtain ⟨S, hS, T, hT, _hd, hdblL⟩ := hL
  
  have hS_eq : S = ({0} : Finset (Fin 2)) := by
    ext a
    rw [← StatMech.mem_dbl_inl S T a, hdblL]
    constructor
    · intro h; simp only [Finset.mem_singleton] at h ⊢; exact Sum.inl_injective h
    · intro h; simp only [Finset.mem_singleton] at h; subst h; decide
  have hT_eq : T = (∅ : Finset (Fin 2)) := by
    ext a
    rw [← StatMech.mem_dbl_inr S T a, hdblL]
    simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
    intro h; exact Sum.inr_ne_inl h
  subst hS_eq hT_eq
  
  rw [StatMech.mem_boxDoubled] at hR
  obtain ⟨S2, hS2, T2, hT2, _hd2, hdblR⟩ := hR
  have hS2_eq : S2 = (∅ : Finset (Fin 2)) := by
    ext a
    rw [← StatMech.mem_dbl_inl S2 T2 a, hdblR]
    simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
    intro h; exact Sum.inl_ne_inr h
  subst hS2_eq
  
  have hempty_mem : (∅ : Finset (Fin 2 ⊕ Fin 2)) ∈ StatMech.boxDoubled 𝒜' ℬ' := by
    rw [StatMech.mem_boxDoubled]
    exact ⟨∅, hS2, ∅, hT, Finset.disjoint_empty_left ∅, rc71_dbl_empty⟩
  rw [hEq] at hempty_mem
  exact rc71_empty_notMem hempty_mem






theorem rc71_witness_not_boxDoubled :
    ¬ rc71_IsBoxDoubled
        (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})) := by
  rw [rc71_witness_compressed_eq]
  exact rc71_disjPreserving_not_boxDoubled.2














theorem rc71_resolveLeft_card_le (i : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n))) :
    (rc71_resolveLeft i Fam).card ≤ Fam.card :=
  Finset.card_image_le






theorem rc71_resolveMember_subset (i : Fin n) (U : Finset (Fin n ⊕ Fin n)) :
    rc71_resolveMember i U ⊆ U := by
  unfold rc71_resolveMember
  split_ifs with h
  · exact Finset.erase_subset _ _
  · exact subset_rfl





theorem rc71_resolveLeft_preserves_other (i j : Fin n) (Fam : Finset (Finset (Fin n ⊕ Fin n)))
    (h : ∀ U ∈ Fam, ¬ (Sum.inl j ∈ U ∧ Sum.inr j ∈ U)) :
    ∀ V ∈ rc71_resolveLeft i Fam, ¬ (Sum.inl j ∈ V ∧ Sum.inr j ∈ V) := by
  intro V hV
  rw [rc71_resolveLeft, Finset.mem_image] at hV
  obtain ⟨U, hU, rfl⟩ := hV
  rintro ⟨hl, hr⟩
  exact h U hU ⟨rc71_resolveMember_subset i U hl, rc71_resolveMember_subset i U hr⟩



open Classical in




theorem rc71_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc70_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 4000 in






























theorem rc71_status :
    
    (∀ (m : ℕ) (i : Fin m) (Fam : Finset (Finset (Fin m ⊕ Fin m))),
        ∀ V ∈ rc71_resolveLeft i Fam, ¬ (Sum.inl i ∈ V ∧ Sum.inr i ∈ V)) ∧
    
    (rc70_DisjPreserving 2
        (rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}))) ∧
    
    ((rc71_disjPreservingCompress 0 (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅})).card
        = (StatMech.boxDoubled ({∅, {0}} : Finset (Finset (Fin 2))) {∅}).card) ∧
    
    (rc70_DisjPreserving 2 ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2)))
        ∧ ¬ rc71_IsBoxDoubled ({{Sum.inl 0}, {Sum.inr 0}} : Finset (Finset (Fin 2 ⊕ Fin 2)))) ∧
    
    (∀ (m : ℕ) (i : Fin m) (Fam : Finset (Finset (Fin m ⊕ Fin m))),
        (rc71_resolveLeft i Fam).card ≤ Fam.card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _m i Fam => rc71_resolveLeft_disjPreserving_at i Fam,
   rc71_witness_disjPreserving,
   rc71_witness_card_preserved,
   rc71_disjPreserving_not_boxDoubled,
   fun _m i Fam => rc71_resolveLeft_card_le i Fam,
   rc71_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
