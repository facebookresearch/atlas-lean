/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.Walls.rc60reimerinjection
import Code.Inequalities.ReimerStep
import Mathlib.Combinatorics.SetFamily.Compression.Down

set_option linter.style.longLine false

open Finset

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]




def rc73_slice0 (i : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter (fun s => i ∉ s)


def rc73_slice1 (i : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter (fun s => i ∈ s)).image (fun s => s.erase i)


@[simp] lemma rc73_mem_slice0 (i : α) (𝒜 : Finset (Finset α)) (s : Finset α) :
    s ∈ rc73_slice0 i 𝒜 ↔ s ∈ 𝒜 ∧ i ∉ s := by
  simp [rc73_slice0, mem_filter]


lemma rc73_mem_slice1 (i : α) (𝒜 : Finset (Finset α)) (s : Finset α) :
    s ∈ rc73_slice1 i 𝒜 ↔ insert i s ∈ 𝒜 ∧ i ∉ s := by
  simp only [rc73_slice1, mem_image, mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hit⟩, rfl⟩
    refine ⟨?_, notMem_erase _ _⟩
    rwa [insert_erase hit]
  · rintro ⟨hs, his⟩
    exact ⟨insert i s, ⟨hs, mem_insert_self _ _⟩, erase_insert his⟩


lemma rc73_slice1_notMem (i : α) (𝒜 : Finset (Finset α)) {s : Finset α}
    (hs : s ∈ rc73_slice1 i 𝒜) : i ∉ s := ((rc73_mem_slice1 i 𝒜 s).mp hs).2


lemma rc73_slice0_notMem (i : α) (𝒜 : Finset (Finset α)) {s : Finset α}
    (hs : s ∈ rc73_slice0 i 𝒜) : i ∉ s := ((rc73_mem_slice0 i 𝒜 s).mp hs).2



lemma rc73_card_present_eq_slice1 (i : α) (𝒜 : Finset (Finset α)) :
    (𝒜.filter (fun s => i ∈ s)).card = (rc73_slice1 i 𝒜).card := by
  unfold rc73_slice1
  rw [Finset.card_image_of_injOn]
  intro s hs t ht hst
  rw [Finset.mem_coe, Finset.mem_filter] at hs ht
  simp only at hst
  have : insert i (s.erase i) = insert i (t.erase i) := by rw [hst]
  rwa [insert_erase hs.2, insert_erase ht.2] at this


lemma rc73_card_eq_slices (i : α) (𝒜 : Finset (Finset α)) :
    𝒜.card = (rc73_slice0 i 𝒜).card + (rc73_slice1 i 𝒜).card := by
  rw [← rc73_card_present_eq_slice1]
  unfold rc73_slice0
  rw [add_comm, Finset.card_filter_add_card_filter_not (p := fun s => i ∈ s)]










def rc73_upComp (i : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (rc73_slice0 i 𝒜 ∩ rc73_slice1 i 𝒜)
    ∪ ((rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜).image (insert i))



lemma rc73_upComp_parts_disjoint (i : α) (𝒜 : Finset (Finset α)) :
    Disjoint (rc73_slice0 i 𝒜 ∩ rc73_slice1 i 𝒜)
      ((rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜).image (insert i)) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  rw [Finset.mem_inter] at hs
  have hi : i ∉ s := rc73_slice0_notMem i 𝒜 hs.1
  rw [Finset.mem_image] at hs'
  obtain ⟨t, _, rfl⟩ := hs'
  exact hi (mem_insert_self _ _)


lemma rc73_card_high (i : α) (𝒜 : Finset (Finset α)) :
    ((rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜).image (insert i)).card
      = (rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜).card := by
  rw [Finset.card_image_of_injOn]
  intro s hs t ht hst
  rw [Finset.mem_coe, Finset.mem_union] at hs ht
  have his : i ∉ s :=
    hs.elim (rc73_slice0_notMem i 𝒜) (rc73_slice1_notMem i 𝒜)
  have hit : i ∉ t :=
    ht.elim (rc73_slice0_notMem i 𝒜) (rc73_slice1_notMem i 𝒜)
  have := congrArg (fun u => Finset.erase u i) hst
  simpa [erase_insert his, erase_insert hit] using this



theorem rc73_upComp_card (i : α) (𝒜 : Finset (Finset α)) :
    (rc73_upComp i 𝒜).card = 𝒜.card := by
  unfold rc73_upComp
  rw [Finset.card_union_of_disjoint (rc73_upComp_parts_disjoint i 𝒜), rc73_card_high,
    Finset.card_inter_add_card_union, rc73_card_eq_slices i 𝒜]










theorem rc73_slice0_box (i : α) (𝒜 ℬ : Finset (Finset α)) :
    rc73_slice0 i (boxFamily 𝒜 ℬ)
      = boxFamily (rc73_slice0 i 𝒜) (rc73_slice0 i ℬ) := by
  ext U
  rw [rc73_mem_slice0, mem_boxFamily, mem_boxFamily]
  constructor
  · rintro ⟨⟨S, hS, T, hT, hd, rfl⟩, hiU⟩
    rw [mem_union, not_or] at hiU
    exact ⟨S, (rc73_mem_slice0 i 𝒜 S).mpr ⟨hS, hiU.1⟩, T,
      (rc73_mem_slice0 i ℬ T).mpr ⟨hT, hiU.2⟩, hd, rfl⟩
  · rintro ⟨S, hS, T, hT, hd, rfl⟩
    rw [rc73_mem_slice0] at hS hT
    exact ⟨⟨S, hS.1, T, hT.1, hd, rfl⟩, by rw [mem_union, not_or]; exact ⟨hS.2, hT.2⟩⟩


theorem rc73_slice1_box (i : α) (𝒜 ℬ : Finset (Finset α)) :
    rc73_slice1 i (boxFamily 𝒜 ℬ)
      = boxFamily (rc73_slice1 i 𝒜) (rc73_slice0 i ℬ)
        ∪ boxFamily (rc73_slice0 i 𝒜) (rc73_slice1 i ℬ) := by
  ext U
  rw [mem_union, mem_boxFamily, mem_boxFamily, rc73_mem_slice1]
  constructor
  · rintro ⟨hbox, hiU⟩
    rw [mem_boxFamily] at hbox
    obtain ⟨S, hS, T, hT, hd, hST⟩ := hbox
    
    have hiST : i ∈ S ∪ T := hST ▸ mem_insert_self i U
    rw [mem_union] at hiST
    rcases hiST with hiS | hiT
    · 
      have hiT : i ∉ T := fun h => (Finset.disjoint_left.mp hd hiS) h
      left
      refine ⟨S.erase i, (rc73_mem_slice1 i 𝒜 (S.erase i)).mpr ⟨?_, notMem_erase _ _⟩, T,
        (rc73_mem_slice0 i ℬ T).mpr ⟨hT, hiT⟩, ?_, ?_⟩
      · rw [insert_erase hiS]; exact hS
      · rw [Finset.disjoint_left]; intro a ha hb
        exact (Finset.disjoint_left.mp hd (mem_of_mem_erase ha)) hb
      · 
        have : U = (S ∪ T).erase i := by rw [hST, erase_insert hiU]
        rw [this, Finset.erase_union_distrib, erase_eq_of_notMem hiT]
    · 
      have hiS : i ∉ S := fun h => (Finset.disjoint_right.mp hd hiT) h
      right
      refine ⟨S, (rc73_mem_slice0 i 𝒜 S).mpr ⟨hS, hiS⟩, T.erase i,
        (rc73_mem_slice1 i ℬ (T.erase i)).mpr ⟨?_, notMem_erase _ _⟩, ?_, ?_⟩
      · rw [insert_erase hiT]; exact hT
      · rw [Finset.disjoint_right]; intro a ha hb
        exact (Finset.disjoint_right.mp hd (mem_of_mem_erase ha)) hb
      · have : U = (S ∪ T).erase i := by rw [hST, erase_insert hiU]
        rw [this, Finset.erase_union_distrib, erase_eq_of_notMem hiS]
  · rintro (⟨S, hS, T, hT, hd, rfl⟩ | ⟨S, hS, T, hT, hd, rfl⟩)
    · rw [rc73_mem_slice1] at hS; rw [rc73_mem_slice0] at hT
      refine ⟨?_, ?_⟩
      · rw [mem_boxFamily]
        refine ⟨insert i S, hS.1, T, hT.1, ?_, ?_⟩
        · rw [Finset.disjoint_insert_left]; exact ⟨hT.2, hd⟩
        · rw [Finset.insert_union]
      · rw [mem_union, not_or]
        exact ⟨hS.2, hT.2⟩
    · rw [rc73_mem_slice0] at hS; rw [rc73_mem_slice1] at hT
      refine ⟨?_, ?_⟩
      · rw [mem_boxFamily]
        refine ⟨S, hS.1, insert i T, hT.1, ?_, ?_⟩
        · rw [Finset.disjoint_insert_right]; exact ⟨hS.2, hd⟩
        · rw [Finset.union_insert]
      · rw [mem_union, not_or]
        exact ⟨hS.2, hT.2⟩




theorem rc73_slice0_upComp (i : α) (𝒜 : Finset (Finset α)) :
    rc73_slice0 i (rc73_upComp i 𝒜) = rc73_slice0 i 𝒜 ∩ rc73_slice1 i 𝒜 := by
  ext s
  rw [rc73_mem_slice0, rc73_upComp, mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨hmem | hmem, his⟩
    · exact hmem
    · rw [mem_image] at hmem
      obtain ⟨t, _, rfl⟩ := hmem
      exact absurd (mem_insert_self i t) his
  · intro hs
    refine ⟨Or.inl hs, ?_⟩
    exact rc73_slice0_notMem i 𝒜 hs.1


theorem rc73_slice1_upComp (i : α) (𝒜 : Finset (Finset α)) :
    rc73_slice1 i (rc73_upComp i 𝒜) = rc73_slice0 i 𝒜 ∪ rc73_slice1 i 𝒜 := by
  ext s
  rw [rc73_mem_slice1, rc73_upComp, mem_union]
  constructor
  · rintro ⟨hmem, his⟩
    rcases hmem with hlo | hhi
    · rw [Finset.mem_inter] at hlo
      exact absurd (mem_insert_self i s) (rc73_slice0_notMem i 𝒜 hlo.1)
    · rw [mem_image] at hhi
      obtain ⟨t, ht, hins⟩ := hhi
      have hit : i ∉ t := by
        rw [mem_union] at ht
        exact ht.elim (rc73_slice0_notMem i 𝒜) (rc73_slice1_notMem i 𝒜)
      have hst : t = s := by
        have := congrArg (fun u => Finset.erase u i) hins
        simpa [erase_insert his, erase_insert hit] using this
      rw [← hst]; exact ht
  · intro hs
    have his : i ∉ s := by
      rw [mem_union] at hs
      exact hs.elim (rc73_slice0_notMem i 𝒜) (rc73_slice1_notMem i 𝒜)
    refine ⟨Or.inr ?_, his⟩
    rw [mem_image]; exact ⟨s, hs, rfl⟩



theorem rc73_absentFiber_subset (i : α) (𝒜 ℬ : Finset (Finset α)) :
    rc73_slice0 i (boxFamily (rc73_upComp i 𝒜) (rc73_upComp i ℬ))
      ⊆ rc73_slice0 i (boxFamily 𝒜 ℬ) := by
  rw [rc73_slice0_box, rc73_slice0_box, rc73_slice0_upComp, rc73_slice0_upComp]
  exact boxFamily_mono Finset.inter_subset_left Finset.inter_subset_left





theorem rc73_presentFiber_subset (i : α) (𝒜 ℬ : Finset (Finset α)) :
    rc73_slice1 i (boxFamily (rc73_upComp i 𝒜) (rc73_upComp i ℬ))
      ⊆ rc73_slice1 i (boxFamily 𝒜 ℬ) := by
  rw [rc73_slice1_box, rc73_slice1_box, rc73_slice0_upComp, rc73_slice1_upComp,
    rc73_slice0_upComp, rc73_slice1_upComp]
  
  intro U hU
  rw [mem_union] at hU ⊢
  set A0 := rc73_slice0 i 𝒜; set A1 := rc73_slice1 i 𝒜
  set B0 := rc73_slice0 i ℬ; set B1 := rc73_slice1 i ℬ
  rcases hU with h | h
  · 
    rw [mem_boxFamily] at h
    obtain ⟨S, hS, T, hT, hd, rfl⟩ := h
    rw [mem_union] at hS
    rw [Finset.mem_inter] at hT
    rcases hS with hS | hS
    · 
      right; rw [mem_boxFamily]; exact ⟨S, hS, T, hT.2, hd, rfl⟩
    · 
      left; rw [mem_boxFamily]; exact ⟨S, hS, T, hT.1, hd, rfl⟩
  · 
    rw [mem_boxFamily] at h
    obtain ⟨S, hS, T, hT, hd, rfl⟩ := h
    rw [Finset.mem_inter] at hS
    rw [mem_union] at hT
    rcases hT with hT | hT
    · 
      left; rw [mem_boxFamily]; exact ⟨S, hS.2, T, hT, hd, rfl⟩
    · 
      right; rw [mem_boxFamily]; exact ⟨S, hS.1, T, hT, hd, rfl⟩









theorem rc73_box_upComp_le (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (boxFamily (rc73_upComp i 𝒜) (rc73_upComp i ℬ)).card ≤ (boxFamily 𝒜 ℬ).card := by
  rw [rc73_card_eq_slices i (boxFamily (rc73_upComp i 𝒜) (rc73_upComp i ℬ)),
    rc73_card_eq_slices i (boxFamily 𝒜 ℬ)]
  exact Nat.add_le_add
    (Finset.card_le_card (rc73_absentFiber_subset i 𝒜 ℬ))
    (Finset.card_le_card (rc73_presentFiber_subset i 𝒜 ℬ))











def rc73_occ {n : ℕ} (𝒜 : Finset (Finset (Fin n))) (K S : Finset (Fin n)) : Bool :=
  decide (∀ S' : Finset (Fin n), S' ∩ K = S ∩ K → S' ∈ 𝒜)




def rc73_disjOcc {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun S =>
    ∃ K L : Finset (Fin n), Disjoint K L ∧ rc73_occ 𝒜 K S = true ∧ rc73_occ ℬ L S = true)






theorem rc73_boxFamily_overcounts :
    2 ^ 2 * (boxFamily reimerStepCexA reimerStepCexB).card
        > (reimerStepCexA.card * reimerStepCexB.card)
    ∧ 2 ^ 2 * (rc73_disjOcc reimerStepCexA reimerStepCexB).card
        ≤ (reimerStepCexA.card * reimerStepCexB.card) := by
  refine ⟨?_, ?_⟩
  · rw [reimerStep_card_box]; decide
  · decide









theorem rc73_disjOcc_downUp_not_monotone_fin3 :
    (rc73_disjOcc (Down.compression 0 ({∅, {0}, {0, 1}, {2}} : Finset (Finset (Fin 3))))
        (rc73_upComp 0 ({∅, {0}, {0, 1}, {0, 2}, {1}, {2}} : Finset (Finset (Fin 3))))).card
      < (rc73_disjOcc ({∅, {0}, {0, 1}, {2}} : Finset (Finset (Fin 3)))
          ({∅, {0}, {0, 1}, {0, 2}, {1}, {2}} : Finset (Finset (Fin 3)))).card := by
  decide



open Classical in




theorem rc73_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc60_reimerWprobCore_of_boxUnionBound h

end StatMech.Walls
