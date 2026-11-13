/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Code.Walls.rc14reimerinduct

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







open Classical in



theorem rc15_reflE_mem_erase (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α) (S : Finset α)
    (haE : a ∈ E) (haS : a ∈ S) :
    S.erase a ∈ rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)
      ↔ S ∈ rc14_reflE E 𝒜 ℬ := by
  rw [rc14_mem_reflE, rc14_mem_reflE, mem_memberSubfamily, mem_nonMemberSubfamily]
  constructor
  · rintro ⟨hsub, ⟨hmem, _⟩, hcompl, hcomplna⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases eq_or_ne x a with rfl | hxa
      · exact haE
      · exact (Finset.mem_erase.mp (hsub (Finset.mem_erase.mpr ⟨hxa, hx⟩))).2
    · rwa [insert_erase haS] at hmem
    · have : E \ S = (E.erase a) \ (S.erase a) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨hxE, hxS⟩
          exact ⟨⟨fun h => hxS (h ▸ haS), hxE⟩, fun h => hxS h.2⟩
        · rintro ⟨⟨hxa, hxE⟩, h⟩
          exact ⟨hxE, fun hxS => h ⟨hxa, hxS⟩⟩
      rwa [this]
  · rintro ⟨hsub, hmem, hcompl⟩
    refine ⟨?_, ⟨?_, by simp [Finset.mem_erase]⟩, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_erase] at hx ⊢
      exact ⟨hx.1, hsub hx.2⟩
    · rwa [insert_erase haS]
    · have : (E.erase a) \ (S.erase a) = E \ S := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hxa, hxE⟩, h⟩
          exact ⟨hxE, fun hxS => h ⟨hxa, hxS⟩⟩
        · rintro ⟨hxE, hxS⟩
          exact ⟨⟨fun h => hxS (h ▸ haS), hxE⟩, fun h => hxS h.2⟩
      rwa [this]
    · simp only [Finset.mem_sdiff, Finset.mem_erase]
      rintro ⟨⟨hcon, _⟩, _⟩; exact hcon rfl

open Classical in




theorem rc15_reflE_mem_id (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α) (S : Finset α)
    (haE : a ∈ E) (haS : a ∉ S) :
    S ∈ rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)
      ↔ S ∈ rc14_reflE E 𝒜 ℬ := by
  rw [rc14_mem_reflE, rc14_mem_reflE, mem_nonMemberSubfamily, mem_memberSubfamily]
  have hcompl : insert a ((E.erase a) \ S) = E \ S := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨⟨_, hxE⟩, hxS⟩)
      · exact ⟨haE, haS⟩
      · exact ⟨hxE, hxS⟩
    · rintro ⟨hxE, hxS⟩
      rcases eq_or_ne x a with rfl | hxa
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hxa, hxE⟩, hxS⟩
  have haEsub : a ∉ (E.erase a) \ S := by simp [Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨hsub, ⟨hmem, _⟩, hcomplmem, _⟩
    refine ⟨?_, hmem, ?_⟩
    · exact hsub.trans (Finset.erase_subset a E)
    · rwa [hcompl] at hcomplmem
  · rintro ⟨hsub, hmem, hcomplmem⟩
    refine ⟨?_, ⟨hmem, haS⟩, ?_, haEsub⟩
    · intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun h => haS (h ▸ hx), hsub hx⟩
    · rw [hcompl]; exact hcomplmem

open Classical in






theorem rc15_card_reflE_slice (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α) (haE : a ∈ E) :
    #(rc14_reflE E 𝒜 ℬ)
      = #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := rc14_reflE E 𝒜 ℬ) (p := fun S => a ∈ S),
    add_comm]
  congr 1
  · 
    apply Finset.card_bij (fun S _ => S)
    · intro S hS
      simp only [Finset.mem_filter] at hS ⊢
      exact (rc15_reflE_mem_id E 𝒜 ℬ a S haE hS.2).mpr hS.1
    · intro S _ S' _ h; exact h
    · intro S hS
      rw [rc14_mem_reflE] at hS
      have haS : a ∉ S := by
        intro h
        have := (Finset.mem_erase.mp (hS.1 h)).1; exact this rfl
      refine ⟨S, ?_, rfl⟩
      simp only [Finset.mem_filter]
      exact ⟨(rc15_reflE_mem_id E 𝒜 ℬ a S haE haS).mp (rc14_mem_reflE _ _ _ _ |>.mpr hS), haS⟩
  · 
    apply Finset.card_bij (fun S _ => S.erase a)
    · intro S hS
      simp only [Finset.mem_filter] at hS
      exact (rc15_reflE_mem_erase E 𝒜 ℬ a S haE hS.2).mpr hS.1
    · intro S hS S' hS' h
      simp only [Finset.mem_filter] at hS hS'
      have := congrArg (insert a) h
      rwa [insert_erase hS.2, insert_erase hS'.2] at this
    · intro R hR
      have hRmem : R ∈ rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a) := hR
      rw [rc14_mem_reflE, mem_memberSubfamily] at hRmem
      obtain ⟨hRsub, ⟨hins, haR⟩, _⟩ := hRmem
      refine ⟨insert a R, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        refine ⟨?_, Finset.mem_insert_self a R⟩
        rw [← rc15_reflE_mem_erase E 𝒜 ℬ a (insert a R) haE (Finset.mem_insert_self a R),
          Finset.erase_insert haR]
        exact hR
      · rw [Finset.erase_insert haR]










def rc15_UpperOn (E : Finset α) (𝒜 : Finset (Finset α)) : Prop :=
  ∀ ⦃S T : Finset α⦄, S ⊆ T → T ⊆ E → S ∈ 𝒜 → T ∈ 𝒜

open Classical in

theorem rc15_upperOn_univ_iff (𝒜 : Finset (Finset α)) :
    rc15_UpperOn univ 𝒜 ↔ IsUpperSet (𝒜 : Set (Finset α)) := by
  constructor
  · intro h S T hST hS
    simp only [Finset.mem_coe] at hS ⊢
    exact h (Finset.le_iff_subset.mp hST) (Finset.subset_univ T) hS
  · intro h S T hST _ hS
    exact h (Finset.le_iff_subset.mpr hST) hS

open Classical in

theorem rc15_upperOn_nonMember {E : Finset α} {𝒜 : Finset (Finset α)}
    (h𝒜 : rc15_UpperOn E 𝒜) (a : α) :
    rc15_UpperOn (E.erase a) (𝒜.nonMemberSubfamily a) := by
  intro S T hST hTE hS
  rw [mem_nonMemberSubfamily] at hS ⊢
  refine ⟨h𝒜 hST (hTE.trans (Finset.erase_subset a E)) hS.1, ?_⟩
  exact fun h => (Finset.mem_erase.mp (hTE h)).1 rfl

open Classical in

theorem rc15_upperOn_member {E : Finset α} {𝒜 : Finset (Finset α)}
    (h𝒜 : rc15_UpperOn E 𝒜) (a : α) (haE : a ∈ E) :
    rc15_UpperOn (E.erase a) (𝒜.memberSubfamily a) := by
  intro S T hST hTE hS
  rw [mem_memberSubfamily] at hS ⊢
  have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTE h)).1 rfl
  refine ⟨?_, haT⟩
  apply h𝒜 (Finset.insert_subset_insert a hST) _ hS.1
  rw [Finset.insert_subset_iff]
  exact ⟨haE, hTE.trans (Finset.erase_subset a E)⟩

open Classical in


theorem rc15_mem_member_of_nonMem {E : Finset α} {𝒜 : Finset (Finset α)} (h𝒜 : rc15_UpperOn E 𝒜)
    (a : α) (haE : a ∈ E) {K : Finset α} (hKE : K ⊆ E) (haK : a ∉ K) (hK : K ∈ 𝒜) :
    K ∈ 𝒜.memberSubfamily a := by
  rw [mem_memberSubfamily]
  refine ⟨?_, haK⟩
  apply h𝒜 (Finset.subset_insert a K) _ hK
  rw [Finset.insert_subset_iff]; exact ⟨haE, hKE⟩

open Classical in






theorem rc15_boxE_mem_erase {𝒜 ℬ : Finset (Finset α)} {E : Finset α}
    (h𝒜 : rc15_UpperOn E 𝒜)
    (a : α) (S : Finset α) (haE : a ∈ E) (haS : a ∈ S) (hSE : S ⊆ E) :
    S.erase a ∈ (rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)
        ∪ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
      ↔ S ∈ rc14_boxE E 𝒜 ℬ := by
  have hSeE : S.erase a ⊆ E.erase a := Finset.erase_subset_erase a hSE
  constructor
  · intro h
    rw [rc14_mem_boxE]
    refine ⟨hSE, ?_⟩
    rw [Finset.mem_union, rc14_mem_boxE, rc14_mem_boxE] at h
    rcases h with ⟨_, K', L', hKL', hK'S, hL'S, hK', hL'⟩ | ⟨_, K', L', hKL', hK'S, hL'S, hK', hL'⟩
    · 
      rw [mem_memberSubfamily] at hK'
      rw [mem_nonMemberSubfamily] at hL'
      refine ⟨insert a K', L', ?_, ?_, ?_, hK'.1, hL'.1⟩
      · rw [Finset.disjoint_insert_left]
        exact ⟨fun haL' => hL'.2 haL', hKL'⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact haS
        · exact Finset.mem_of_mem_erase (hK'S hx)
      · intro x hx; exact Finset.mem_of_mem_erase (hL'S hx)
    · 
      rw [mem_nonMemberSubfamily] at hK'
      rw [mem_memberSubfamily] at hL'
      refine ⟨K', insert a L', ?_, ?_, ?_, hK'.1, hL'.1⟩
      · rw [Finset.disjoint_insert_right]
        exact ⟨fun haK' => hK'.2 haK', hKL'⟩
      · intro x hx; exact Finset.mem_of_mem_erase (hK'S hx)
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact haS
        · exact Finset.mem_of_mem_erase (hL'S hx)
  · intro h
    rw [rc14_mem_boxE] at h
    obtain ⟨_, K, L, hKL, hKS, hLS, hK, hL⟩ := h
    rw [Finset.mem_union, rc14_mem_boxE, rc14_mem_boxE]
    by_cases haK : a ∈ K
    · 
      have haL : a ∉ L := fun h => (Finset.disjoint_left.mp hKL haK) h
      left
      refine ⟨hSeE, K.erase a, L, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Finset.disjoint_left.mpr fun x hx hxL =>
          (Finset.disjoint_left.mp hKL (Finset.mem_of_mem_erase hx)) hxL)
      · exact Finset.erase_subset_erase a hKS
      · intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun h => haL (h ▸ hx), hLS hx⟩
      · rw [mem_memberSubfamily, insert_erase haK]; exact ⟨hK, Finset.notMem_erase a K⟩
      · rw [mem_nonMemberSubfamily]; exact ⟨hL, haL⟩
    by_cases haL : a ∈ L
    · 
      right
      refine ⟨hSeE, K, L.erase a, ?_, ?_, ?_, ?_, ?_⟩
      · exact (Finset.disjoint_right.mpr fun x hx hxK =>
          (Finset.disjoint_right.mp hKL (Finset.mem_of_mem_erase hx)) hxK)
      · intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun h => haK (h ▸ hx), hKS hx⟩
      · exact Finset.erase_subset_erase a hLS
      · rw [mem_nonMemberSubfamily]; exact ⟨hK, haK⟩
      · rw [mem_memberSubfamily, insert_erase haL]; exact ⟨hL, Finset.notMem_erase a L⟩
    · 
      left
      refine ⟨hSeE, K, L, hKL, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun h => haK (h ▸ hx), hKS hx⟩
      · intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun h => haL (h ▸ hx), hLS hx⟩
      · exact rc15_mem_member_of_nonMem h𝒜 a haE (hKS.trans hSE) haK hK
      · rw [mem_nonMemberSubfamily]; exact ⟨hL, haL⟩

open Classical in



theorem rc15_boxE_mem_id (𝒜 ℬ : Finset (Finset α)) (E : Finset α) (a : α) (S : Finset α)
    (haS : a ∉ S) (hSE : S ⊆ E) :
    S ∈ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a)
      ↔ S ∈ rc14_boxE E 𝒜 ℬ := by
  rw [rc14_mem_boxE, rc14_mem_boxE]
  constructor
  · rintro ⟨_, K, L, hKL, hKS, hLS, hK, hL⟩
    rw [mem_nonMemberSubfamily] at hK hL
    exact ⟨hSE, K, L, hKL, hKS, hLS, hK.1, hL.1⟩
  · rintro ⟨_, K, L, hKL, hKS, hLS, hK, hL⟩
    have hKSe : K ⊆ E.erase a := by
      intro x hx; rw [Finset.mem_erase]; exact ⟨fun h => haS (h ▸ hKS hx), hSE (hKS hx)⟩
    refine ⟨?_, K, L, hKL, hKS, hLS, ?_, ?_⟩
    · intro x hx; rw [Finset.mem_erase]; exact ⟨fun h => haS (h ▸ hx), hSE hx⟩
    · rw [mem_nonMemberSubfamily]; exact ⟨hK, fun h => haS (hKS h)⟩
    · rw [mem_nonMemberSubfamily]; exact ⟨hL, fun h => haS (hLS h)⟩

open Classical in






theorem rc15_card_boxE_slice {𝒜 ℬ : Finset (Finset α)} {E : Finset α} (h𝒜 : rc15_UpperOn E 𝒜)
    (a : α) (haE : a ∈ E) :
    #(rc14_boxE E 𝒜 ℬ)
      = #(rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)
            ∪ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := rc14_boxE E 𝒜 ℬ) (p := fun S => a ∈ S),
    add_comm]
  congr 1
  · 
    apply Finset.card_bij (fun S _ => S)
    · intro S hS
      simp only [Finset.mem_filter] at hS
      have hSE : S ⊆ E := (rc14_mem_boxE _ _ _ _).mp hS.1 |>.1
      exact (rc15_boxE_mem_id 𝒜 ℬ E a S hS.2 hSE).mpr hS.1
    · intro S _ S' _ h; exact h
    · intro S hS
      have hSE : S ⊆ E.erase a := (rc14_mem_boxE _ _ _ _).mp hS |>.1
      have haS : a ∉ S := fun h => (Finset.mem_erase.mp (hSE h)).1 rfl
      refine ⟨S, ?_, rfl⟩
      simp only [Finset.mem_filter]
      refine ⟨(rc15_boxE_mem_id 𝒜 ℬ E a S haS (hSE.trans (Finset.erase_subset a E))).mp hS, haS⟩
  · 
    apply Finset.card_bij (fun S _ => S.erase a)
    · intro S hS
      simp only [Finset.mem_filter] at hS
      have hSE : S ⊆ E := (rc14_mem_boxE _ _ _ _).mp hS.1 |>.1
      exact (rc15_boxE_mem_erase h𝒜 a S haE hS.2 hSE).mpr hS.1
    · intro S hS S' hS' h
      simp only [Finset.mem_filter] at hS hS'
      have := congrArg (insert a) h
      rwa [insert_erase hS.2, insert_erase hS'.2] at this
    · intro R hR
      have hRsub : R ⊆ E.erase a := by
        rcases Finset.mem_union.mp hR with h | h <;>
          exact (rc14_mem_boxE _ _ _ _).mp h |>.1
      have haR : a ∉ R := fun h => (Finset.mem_erase.mp (hRsub h)).1 rfl
      refine ⟨insert a R, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        refine ⟨?_, Finset.mem_insert_self a R⟩
        rw [← rc15_boxE_mem_erase h𝒜 a (insert a R) haE (Finset.mem_insert_self a R)
          (by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact haE
            · exact Finset.mem_of_mem_erase (hRsub hx)),
          Finset.erase_insert haR]
        exact hR
      · rw [Finset.erase_insert haR]








open Classical in

theorem rc15_reflE_left_subset {E : Finset α} {𝒜 𝒜' ℬ : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') :
    rc14_reflE E 𝒜 ℬ ⊆ rc14_reflE E 𝒜' ℬ := by
  intro S hS
  rw [rc14_mem_reflE] at hS ⊢
  exact ⟨hS.1, h hS.2.1, hS.2.2⟩

open Classical in



theorem rc15_reflE_nonMem_subset_mem {E : Finset α} {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : rc15_UpperOn E 𝒜) (a : α) (haE : a ∈ E) :
    rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) ℬ
      ⊆ rc14_reflE (E.erase a) (𝒜.memberSubfamily a) ℬ := by
  intro S hS
  rw [rc14_mem_reflE] at hS ⊢
  obtain ⟨hSF, hS𝒜, hSℬ⟩ := hS
  rw [mem_nonMemberSubfamily] at hS𝒜
  refine ⟨hSF, ?_, hSℬ⟩
  exact rc15_mem_member_of_nonMem h𝒜 a haE (hSF.trans (Finset.erase_subset a E)) hS𝒜.2 hS𝒜.1

open Classical in

theorem rc15_card_reflE_nonMem_le_mem {E : Finset α} {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : rc15_UpperOn E 𝒜) (a : α) (haE : a ∈ E) :
    #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) ℬ)
      ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) ℬ) :=
  Finset.card_le_card (rc15_reflE_nonMem_subset_mem h𝒜 a haE)





def rc15_BKRground (E : Finset α) : Prop :=
  ∀ 𝒜 ℬ : Finset (Finset α), rc15_UpperOn E 𝒜 → rc15_UpperOn E ℬ →
    #(rc14_boxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)









def rc15_SliceUnionBound : Prop :=
  ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E →
    rc15_UpperOn E 𝒜 → rc15_UpperOn E ℬ →
      #(rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)
          ∪ rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))



open Classical in



theorem rc15_bkrground_empty : rc15_BKRground (∅ : Finset α) := by
  intro 𝒜 ℬ _ _
  apply Finset.card_le_card
  intro S hS
  rw [rc14_mem_boxE] at hS
  obtain ⟨hSE, K, L, _, hKS, hLS, hK, hL⟩ := hS
  have hS0 : S = ∅ := Finset.subset_empty.mp hSE
  subst hS0
  have hK0 : K = ∅ := Finset.subset_empty.mp hKS
  have hL0 : L = ∅ := Finset.subset_empty.mp hLS
  subst hK0; subst hL0
  rw [rc14_mem_reflE]
  refine ⟨Finset.Subset.refl _, hK, ?_⟩
  simpa using hL



open Classical in





theorem rc15_bkrground_step {E : Finset α} (hUnion : rc15_SliceUnionBound (α := α)) {a : α}
    (haE : a ∈ E) (hIH : rc15_BKRground (E.erase a)) : rc15_BKRground E := by
  intro 𝒜 ℬ h𝒜 hℬ
  set F := E.erase a with hF
  set 𝒜₀ := 𝒜.nonMemberSubfamily a
  set 𝒜₁ := 𝒜.memberSubfamily a
  set ℬ₀ := ℬ.nonMemberSubfamily a
  set ℬ₁ := ℬ.memberSubfamily a
  rw [rc15_card_boxE_slice h𝒜 a haE, rc15_card_reflE_slice E 𝒜 ℬ a haE]
  
  have hIH00 : #(rc14_boxE F 𝒜₀ ℬ₀) ≤ #(rc14_reflE F 𝒜₀ ℬ₀) :=
    hIH 𝒜₀ ℬ₀ (rc15_upperOn_nonMember h𝒜 a) (rc15_upperOn_nonMember hℬ a)
  
  have hmono : #(rc14_reflE F 𝒜₀ ℬ₀) ≤ #(rc14_reflE F 𝒜₁ ℬ₀) :=
    rc15_card_reflE_nonMem_le_mem h𝒜 a haE
  
  have hres : #(rc14_boxE F 𝒜₁ ℬ₀ ∪ rc14_boxE F 𝒜₀ ℬ₁) ≤ #(rc14_reflE F 𝒜₀ ℬ₁) :=
    hUnion E 𝒜 ℬ a haE h𝒜 hℬ
  
  calc #(rc14_boxE F 𝒜₀ ℬ₀) + #(rc14_boxE F 𝒜₁ ℬ₀ ∪ rc14_boxE F 𝒜₀ ℬ₁)
      ≤ #(rc14_reflE F 𝒜₁ ℬ₀) + #(rc14_reflE F 𝒜₀ ℬ₁) := by
        exact Nat.add_le_add (le_trans hIH00 hmono) hres
    _ = #(rc14_reflE F 𝒜₀ ℬ₁) + #(rc14_reflE F 𝒜₁ ℬ₀) := Nat.add_comm _ _

open Classical in




theorem rc15_bkrground_of_sliceUnion (hUnion : rc15_SliceUnionBound (α := α)) :
    ∀ E : Finset α, rc15_BKRground E := by
  intro E
  induction E using Finset.strongInduction with
  | _ E ih =>
    rcases E.eq_empty_or_nonempty with rfl | ⟨a, haE⟩
    · exact rc15_bkrground_empty
    · exact rc15_bkrground_step hUnion haE (ih (E.erase a) (Finset.erase_ssubset haE))








open Classical in

theorem rc15_boxE_univ (𝒜 ℬ : Finset (Finset α)) :
    rc14_boxE (univ : Finset α) 𝒜 ℬ = rc10_boxSupp 𝒜 ℬ := by
  ext S
  rw [rc14_mem_boxE, rc11_mem_boxSupp]
  simp only [Finset.subset_univ, true_and]

open Classical in

theorem rc15_reflE_univ (𝒜 ℬ : Finset (Finset α)) :
    rc14_reflE (univ : Finset α) 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
  ext S
  rw [rc14_mem_reflE, rc11_mem_reflInter]
  simp only [Finset.subset_univ, true_and, Finset.compl_eq_univ_sdiff]

open Classical in



theorem rc15_bkrSetFamily_of_bkrground (h : ∀ (β : Type) [Fintype β] [DecidableEq β],
    rc15_BKRground (univ : Finset β)) : rc10_BKRSetFamily := by
  intro n 𝒜 ℬ h𝒜 hℬ
  have := h (Fin n) 𝒜 ℬ ((rc15_upperOn_univ_iff 𝒜).mpr h𝒜) ((rc15_upperOn_univ_iff ℬ).mpr hℬ)
  rwa [rc15_boxE_univ, rc15_reflE_univ] at this



open Classical in






theorem rc15_bkrSetFamily_of_sliceUnion
    (hUnion : ∀ (β : Type) [Fintype β] [DecidableEq β], rc15_SliceUnionBound (α := β)) :
    rc10_BKRSetFamily :=
  rc15_bkrSetFamily_of_bkrground
    (fun β _ _ => rc15_bkrground_of_sliceUnion (hUnion β) univ)








open Classical in



theorem rc15_sliceUnion_empty_left {E : Finset α} (ℬ : Finset (Finset α)) (a : α) :
    #(rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).memberSubfamily a) (ℬ.nonMemberSubfamily a)
        ∪ rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).nonMemberSubfamily a) (ℬ.memberSubfamily a))
      ≤ #(rc14_reflE (E.erase a) ((∅ : Finset (Finset α)).nonMemberSubfamily a)
          (ℬ.memberSubfamily a)) := by
  have hbox : ∀ ℬ' : Finset (Finset α),
      rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).memberSubfamily a) ℬ' = ∅ := by
    intro ℬ'
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    rw [rc14_mem_boxE] at hS
    obtain ⟨_, K, _, _, _, _, hK, _⟩ := hS
    rw [mem_memberSubfamily] at hK
    exact absurd hK.1 (by simp)
  have hbox2 : ∀ ℬ' : Finset (Finset α),
      rc14_boxE (E.erase a) ((∅ : Finset (Finset α)).nonMemberSubfamily a) ℬ' = ∅ := by
    intro ℬ'
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    rw [rc14_mem_boxE] at hS
    obtain ⟨_, K, _, _, _, _, hK, _⟩ := hS
    rw [mem_nonMemberSubfamily] at hK
    exact absurd hK.1 (by simp)
  rw [hbox, hbox2, Finset.union_empty]
  simp

end StatMech.Walls
