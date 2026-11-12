/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Code.Walls.rc49doubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










theorem rc50_jointImage_inter_complKL (S K L : Finset α) :
    rc49_jointImage S K L ∩ (K ∪ L)ᶜ = S ∩ (K ∪ L)ᶜ := by
  ext a
  simp only [rc49_jointImage, Finset.mem_inter, Finset.mem_union, Finset.mem_compl,
    Finset.mem_union]
  tauto







theorem rc50_jointImage_involutive (S K L : Finset α) (hKL : Disjoint K L) :
    rc49_jointImage (rc49_jointImage S K L) K L = S := by
  ext a
  have hd : a ∈ K → a ∉ L := fun h => Finset.disjoint_left.mp hKL h
  simp only [rc49_jointImage, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
    Finset.mem_union]
  tauto






theorem rc50_jointImage_injective_of_fixed_witness (K L : Finset α) (hKL : Disjoint K L) :
    Function.Injective (fun S => rc49_jointImage S K L) := by
  intro S S' h
  have h1 := rc50_jointImage_involutive S K L hKL
  have h2 := rc50_jointImage_involutive S' K L hKL
  simp only at h
  rw [← h1, ← h2, h]








open Classical in




theorem rc50_jointImage_mem_neighbourhood {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L)
    (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    rc49_jointImage S K L ∈ rc49_neighbourhood 𝒜 ℬ S := by
  rw [rc49_neighbourhood, Finset.mem_filter]
  exact ⟨rc49_jointImage_mem_reflInter hKL hKA hLB, K, L, hKL, hKA, hLB, rfl⟩

open Classical in







theorem rc50_block_hall {𝒜 ℬ : Finset (Finset α)} {W : Finset (Finset α)} {K L : Finset α}
    (hKL : Disjoint K L)
    (hW : ∀ S ∈ W, (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ)) :
    #W ≤ #(W.biUnion (rc49_neighbourhood 𝒜 ℬ)) := by
  refine Finset.card_le_card_of_injOn (fun S => rc49_jointImage S K L) ?_ ?_
  · intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_biUnion]
    obtain ⟨hKA, hLB⟩ := hW S hS
    exact ⟨S, hS, rc50_jointImage_mem_neighbourhood hKL hKA hLB⟩
  · intro S _ S' _ h
    exact rc50_jointImage_injective_of_fixed_witness K L hKL h







open Classical in





def rc50_InjectiveSelection (𝒜 ℬ : Finset (Finset α)) : Prop :=
  ∃ w : Finset α → Finset α × Finset α,
    (∀ S ∈ rc20_famCylBox 𝒜 ℬ, Disjoint (w S).1 (w S).2 ∧
      (∀ T : Finset α, T ∩ (w S).1 = S ∩ (w S).1 → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ (w S).2 = S ∩ (w S).2 → T ∈ ℬ)) ∧
    Set.InjOn (fun S => rc49_jointImage S (w S).1 (w S).2) (rc20_famCylBox 𝒜 ℬ)

open Classical in





theorem rc50_wall_of_injectiveSelection {𝒜 ℬ : Finset (Finset α)}
    (h : rc50_InjectiveSelection 𝒜 ℬ) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  obtain ⟨w, hwit, hinj⟩ := h
  refine Finset.card_le_card_of_injOn (fun S => rc49_jointImage S (w S).1 (w S).2) ?_ hinj
  intro S hS
  rw [Finset.mem_coe] at hS
  obtain ⟨hKL, hKA, hLB⟩ := hwit S hS
  exact rc49_jointImage_mem_reflInter hKL hKA hLB

open Classical in





theorem rc50_hall_of_injectiveSelection {𝒜 ℬ : Finset (Finset α)}
    (h : rc50_InjectiveSelection 𝒜 ℬ) : rc49_HallCond 𝒜 ℬ := by
  obtain ⟨w, hwit, hinj⟩ := h
  intro W hW
  refine Finset.card_le_card_of_injOn (fun S => rc49_jointImage S (w S).1 (w S).2) ?_ ?_
  · intro S hSW
    rw [Finset.mem_coe] at hSW
    have hSbox : S ∈ rc20_famCylBox 𝒜 ℬ := hW hSW
    obtain ⟨hKL, hKA, hLB⟩ := hwit S hSbox
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨S, hSW, rc50_jointImage_mem_neighbourhood hKL hKA hLB⟩
  · intro S hSW S' hSW' heq
    rw [Finset.mem_coe] at hSW hSW'
    exact hinj (hW hSW) (hW hSW') heq

open Classical in







theorem rc50_injectiveSelection_of_hall {𝒜 ℬ : Finset (Finset α)}
    (h : rc49_HallCond 𝒜 ℬ) : rc50_InjectiveSelection 𝒜 ℬ := by
  let box := rc20_famCylBox 𝒜 ℬ
  
  let t : {S : Finset α // S ∈ box} → Finset (Finset α) :=
    fun S => rc49_neighbourhood 𝒜 ℬ S.1
  have hHall : ∀ s : Finset {S : Finset α // S ∈ box}, #s ≤ #(s.biUnion t) := by
    intro s
    have hsub : s.image (Subtype.val) ⊆ box := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨y, _, rfl⟩ := hx; exact y.2
    have hcard_s : #s = #(s.image (Subtype.val)) := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
    have hbiU : (s.image (Subtype.val)).biUnion (rc49_neighbourhood 𝒜 ℬ) = s.biUnion t := by
      ext R; simp only [Finset.mem_biUnion, Finset.mem_image, t]
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, hR⟩; exact ⟨y, hy, hR⟩
      · rintro ⟨y, hy, hR⟩; exact ⟨y.1, ⟨y, hy, rfl⟩, hR⟩
    rw [hcard_s, ← hbiU]; exact h _ hsub
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  
  have hchoose : ∀ S : {S : Finset α // S ∈ box}, ∃ p : Finset α × Finset α,
      Disjoint p.1 p.2 ∧
      (∀ T : Finset α, T ∩ p.1 = S.1 ∩ p.1 → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ p.2 = S.1 ∩ p.2 → T ∈ ℬ) ∧
      rc49_jointImage S.1 p.1 p.2 = f S := by
    intro S
    have hmem := hfmem S
    simp only [t, rc49_neighbourhood, Finset.mem_filter] at hmem
    obtain ⟨_, K, L, hKL, hKA, hLB, hEq⟩ := hmem
    exact ⟨(K, L), hKL, hKA, hLB, hEq⟩
  choose g hg using hchoose
  
  set w : Finset α → Finset α × Finset α := fun S => if hS : S ∈ box then g ⟨S, hS⟩ else (∅, ∅)
    with hw
  have hwbox : ∀ (S : Finset α) (hS : S ∈ box), w S = g ⟨S, hS⟩ := by
    intro S hS; rw [hw]; simp only [dif_pos hS]
  refine ⟨w, ?_, ?_⟩
  · intro S hS
    have hSbox : S ∈ box := hS
    rw [hwbox S hSbox]
    obtain ⟨hKL, hKA, hLB, _⟩ := hg ⟨S, hSbox⟩
    exact ⟨hKL, hKA, hLB⟩
  · intro S hS S' hS' heq
    have hSbox : S ∈ box := hS
    have hSbox' : S' ∈ box := hS'
    simp only [hwbox S hSbox, hwbox S' hSbox'] at heq
    have e1 := (hg ⟨S, hSbox⟩).2.2.2
    have e2 := (hg ⟨S', hSbox'⟩).2.2.2
    rw [e1, e2] at heq
    exact congrArg Subtype.val (hfinj heq)

open Classical in




theorem rc50_hall_iff_injectiveSelection (𝒜 ℬ : Finset (Finset α)) :
    rc49_HallCond 𝒜 ℬ ↔ rc50_InjectiveSelection 𝒜 ℬ :=
  ⟨rc50_injectiveSelection_of_hall, rc50_hall_of_injectiveSelection⟩





open Classical in



def rc50_InjectiveSelectionAll : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))), rc50_InjectiveSelection 𝒜 ℬ

open Classical in



theorem rc50_reimer_closes_of_injectiveSelectionAll (h : rc50_InjectiveSelectionAll) :
    rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue
    (fun n 𝒜 ℬ => rc50_wall_of_injectiveSelection (h n 𝒜 ℬ))

open Classical in




theorem rc50_injectiveSelectionAll_iff_hallDoubled :
    rc50_InjectiveSelectionAll ↔ rc49_HallDoubled := by
  constructor
  · intro h n 𝒜 ℬ; exact (rc50_hall_iff_injectiveSelection 𝒜 ℬ).mpr (h n 𝒜 ℬ)
  · intro h n 𝒜 ℬ; exact (rc50_hall_iff_injectiveSelection 𝒜 ℬ).mp (h n 𝒜 ℬ)











set_option maxRecDepth 4000 in


theorem rc50_box_residual_eq :
    rc20_famCylBox rc48_A₂ rc48_B₂ = {(∅ : Finset (Fin 3))} := by
  rw [← rc20_famCylBoxComp_eq, rc48_A₂, rc48_B₂]; decide

open Classical in






theorem rc50_injectiveSelection_residual :
    rc50_InjectiveSelection rc48_A₂ rc48_B₂ := by
  refine ⟨fun _ => ({1, 2}, {0}), ?_, ?_⟩
  · intro S hS
    rw [rc50_box_residual_eq, Finset.mem_singleton] at hS
    subst hS
    exact ⟨by decide, rc49_residual_KcylA, rc49_residual_LcylB⟩
  · intro S hS S' hS' _
    rw [Finset.mem_coe, rc50_box_residual_eq, Finset.mem_singleton] at hS hS'
    rw [hS, hS']

open Classical in





theorem rc50_hall_residual : rc49_HallCond rc48_A₂ rc48_B₂ :=
  rc50_hall_of_injectiveSelection rc50_injectiveSelection_residual



open Classical in


































theorem rc50_reimer_involution_and_selection :
    (∀ (S K L : Finset (Fin 3)), Disjoint K L →
        rc49_jointImage (rc49_jointImage S K L) K L = S)
      ∧ (∀ (K L : Finset (Fin 3)), Disjoint K L →
          Function.Injective (fun S => rc49_jointImage S K L))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          rc49_HallCond 𝒜 ℬ ↔ rc50_InjectiveSelection 𝒜 ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          rc50_InjectiveSelection 𝒜 ℬ →
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc50_InjectiveSelectionAll ↔ rc49_HallDoubled)
      ∧ (rc50_InjectiveSelectionAll → rc18_CylBoxReflInter)
      ∧ rc50_InjectiveSelection rc48_A₂ rc48_B₂
      ∧ rc49_HallCond rc48_A₂ rc48_B₂ :=
  ⟨fun S K L hKL => rc50_jointImage_involutive S K L hKL,
    fun K L hKL => rc50_jointImage_injective_of_fixed_witness K L hKL,
    fun 𝒜 ℬ => rc50_hall_iff_injectiveSelection 𝒜 ℬ,
    fun _ _ h => rc50_wall_of_injectiveSelection h,
    rc50_injectiveSelectionAll_iff_hallDoubled,
    rc50_reimer_closes_of_injectiveSelectionAll,
    rc50_injectiveSelection_residual,
    rc50_hall_residual⟩

end StatMech.Walls
