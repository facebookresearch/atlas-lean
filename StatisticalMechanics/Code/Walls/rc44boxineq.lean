/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































































import Code.Walls.rc43reimer
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








open Classical in



noncomputable def rc44_famCylBoxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    Finset (Finset α) :=
  E.powerset.filter (fun S => ∃ K L : Finset α, K ⊆ E ∧ L ⊆ E ∧ Disjoint K L ∧
    (∀ T ⊆ E, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
    (∀ T ⊆ E, T ∩ L = S ∩ L → T ∈ ℬ))

open Classical in



noncomputable def rc44_reflInterE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    Finset (Finset α) :=
  E.powerset.filter (fun R => R ∈ 𝒜 ∧ E \ R ∈ ℬ)


def rc44_slab0 (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.filter (fun S => a ∉ S)


def rc44_slab1 (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  (𝒜.filter (fun S => a ∈ S)).image (fun S => S.erase a)

open Classical in

theorem rc44_mem_famCylBoxE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc44_famCylBoxE E 𝒜 ℬ ↔
      S ⊆ E ∧ ∃ K L : Finset α, K ⊆ E ∧ L ⊆ E ∧ Disjoint K L ∧
        (∀ T ⊆ E, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
        (∀ T ⊆ E, T ∩ L = S ∩ L → T ∈ ℬ) := by
  rw [rc44_famCylBoxE, Finset.mem_filter, Finset.mem_powerset]

open Classical in

theorem rc44_mem_reflInterE (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (R : Finset α) :
    R ∈ rc44_reflInterE E 𝒜 ℬ ↔ R ⊆ E ∧ R ∈ 𝒜 ∧ E \ R ∈ ℬ := by
  rw [rc44_reflInterE, Finset.mem_filter, Finset.mem_powerset]








open Classical in


theorem rc44_famCylBoxE_univ (𝒜 ℬ : Finset (Finset α)) :
    rc44_famCylBoxE Finset.univ 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
  ext S
  rw [rc44_mem_famCylBoxE, rc20_famCylBox, Finset.mem_filter]
  refine ⟨fun h => ⟨Finset.mem_univ _, ?_⟩, fun h => ⟨Finset.subset_univ _, ?_⟩⟩
  · obtain ⟨_, K, L, _, _, hKL, hKA, hLB⟩ := h
    exact ⟨K, L, hKL, fun T => hKA T (Finset.subset_univ T),
      fun T => hLB T (Finset.subset_univ T)⟩
  · obtain ⟨_, K, L, hKL, hKA, hLB⟩ := h
    exact ⟨K, L, Finset.subset_univ K, Finset.subset_univ L, hKL,
      fun T _ => hKA T, fun T _ => hLB T⟩

open Classical in


theorem rc44_reflInterE_univ (𝒜 ℬ : Finset (Finset α)) :
    rc44_reflInterE Finset.univ 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
  ext R
  rw [rc44_mem_reflInterE, rc20_mem_reflInter, ← compl_eq_univ_sdiff]
  simp only [Finset.subset_univ, true_and]



omit [Fintype α] in

theorem rc44_mem_slab0 (a : α) (𝒜 : Finset (Finset α)) (S : Finset α) :
    S ∈ rc44_slab0 a 𝒜 ↔ S ∈ 𝒜 ∧ a ∉ S := by
  rw [rc44_slab0, Finset.mem_filter]

omit [Fintype α] in

theorem rc44_mem_slab1 (a : α) (𝒜 : Finset (Finset α)) (S : Finset α) :
    S ∈ rc44_slab1 a 𝒜 ↔ ∃ U ∈ 𝒜, a ∈ U ∧ U.erase a = S := by
  rw [rc44_slab1, Finset.mem_image]
  constructor
  · rintro ⟨U, hU, rfl⟩
    rw [Finset.mem_filter] at hU
    exact ⟨U, hU.1, hU.2, rfl⟩
  · rintro ⟨U, hU, haU, rfl⟩
    exact ⟨U, Finset.mem_filter.mpr ⟨hU, haU⟩, rfl⟩

omit [Fintype α] in


theorem rc44_inter_erase_of_not_mem (T K : Finset α) (a : α) (ha : a ∉ T) :
    T ∩ K.erase a = T ∩ K := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨hxT, _, hxK⟩; exact ⟨hxT, hxK⟩
  · rintro ⟨hxT, hxK⟩; exact ⟨hxT, fun h => ha (h ▸ hxT), hxK⟩

omit [Fintype α] in

theorem rc44_disjoint_erase (K L : Finset α) (a : α) (h : Disjoint K L) :
    Disjoint (K.erase a) (L.erase a) :=
  Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
    (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) h)










open Classical in



theorem rc44_slab0_famCylBoxE_subset (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)) :
    rc44_slab0 a (rc44_famCylBoxE E 𝒜 ℬ)
      ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ) := by
  intro S hS
  rw [rc44_mem_slab0] at hS
  obtain ⟨hSbox, haS⟩ := hS
  rw [rc44_mem_famCylBoxE] at hSbox
  obtain ⟨hSE, K, L, hKE, hLE, hKL, hKA, hLB⟩ := hSbox
  rw [rc44_mem_famCylBoxE]
  refine ⟨Finset.subset_erase.mpr ⟨hSE, haS⟩, K.erase a, L.erase a,
    Finset.erase_subset_erase a hKE, Finset.erase_subset_erase a hLE,
    rc44_disjoint_erase K L a hKL, ?_, ?_⟩
  · 
    intro T hT hTtrace
    have haT : a ∉ T := (Finset.subset_erase.mp hT).2
    have hTE : T ⊆ E := (Finset.subset_erase.mp hT).1
    have hTK : T ∩ K = S ∩ K := by
      rw [← rc44_inter_erase_of_not_mem T K a haT, ← rc44_inter_erase_of_not_mem S K a haS]
      exact hTtrace
    rw [rc44_mem_slab0]
    exact ⟨hKA T hTE hTK, haT⟩
  · 
    intro T hT hTtrace
    have haT : a ∉ T := (Finset.subset_erase.mp hT).2
    have hTE : T ⊆ E := (Finset.subset_erase.mp hT).1
    have hTL : T ∩ L = S ∩ L := by
      rw [← rc44_inter_erase_of_not_mem T L a haT, ← rc44_inter_erase_of_not_mem S L a haS]
      exact hTtrace
    rw [rc44_mem_slab0]
    exact ⟨hLB T hTE hTL, haT⟩

omit [Fintype α] in


theorem rc44_inter_insert (T' K U : Finset α) (a : α) (haU : a ∈ U)
    (htrace : T' ∩ K.erase a = U.erase a ∩ K.erase a) :
    (insert a T') ∩ K = U ∩ K := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  by_cases hx : x = a
  · subst hx
    exact ⟨fun h => ⟨haU, h.2⟩, fun h => ⟨Or.inl rfl, h.2⟩⟩
  · have hxe : ∀ F : Finset α, (x ∈ F.erase a) ↔ x ∈ F := fun F => by
      rw [Finset.mem_erase]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    constructor
    · rintro ⟨hxi, hxK⟩
      rcases hxi with h | hxT'
      · exact absurd h hx
      · have : x ∈ T' ∩ K.erase a := Finset.mem_inter.mpr ⟨hxT', (hxe K).mpr hxK⟩
        rw [htrace, Finset.mem_inter] at this
        exact ⟨(hxe U).mp this.1, hxK⟩
    · rintro ⟨hxU, hxK⟩
      have : x ∈ U.erase a ∩ K.erase a := Finset.mem_inter.mpr ⟨(hxe U).mpr hxU, (hxe K).mpr hxK⟩
      rw [← htrace, Finset.mem_inter] at this
      exact ⟨Or.inr this.1, hxK⟩

open Classical in






theorem rc44_slab1_famCylBoxE_subset (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)) :
    rc44_slab1 a (rc44_famCylBoxE E 𝒜 ℬ)
      ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ) := by
  intro S hS
  rw [rc44_mem_slab1] at hS
  obtain ⟨U, hUbox, haU, rfl⟩ := hS
  rw [rc44_mem_famCylBoxE] at hUbox
  obtain ⟨hUE, K, L, hKE, hLE, hKL, hKA, hLB⟩ := hUbox
  have haE : a ∈ E := hUE haU
  rw [rc44_mem_famCylBoxE]
  refine ⟨Finset.erase_subset_erase a hUE, K.erase a, L.erase a,
    Finset.erase_subset_erase a hKE, Finset.erase_subset_erase a hLE,
    rc44_disjoint_erase K L a hKL, ?_, ?_⟩
  · 
    intro T hT hTtrace
    have haT : a ∉ T := (Finset.subset_erase.mp hT).2
    have hTsub : T ⊆ E := (Finset.subset_erase.mp hT).1
    have hInsE : insert a T ⊆ E := Finset.insert_subset haE hTsub
    have hInsAK : insert a T ∩ K = U ∩ K := rc44_inter_insert T K U a haU hTtrace
    have hInsA : insert a T ∈ 𝒜 := hKA (insert a T) hInsE hInsAK
    rw [rc44_mem_slab1]
    exact ⟨insert a T, hInsA, Finset.mem_insert_self a T, Finset.erase_insert haT⟩
  · 
    intro T hT hTtrace
    have haT : a ∉ T := (Finset.subset_erase.mp hT).2
    have hTsub : T ⊆ E := (Finset.subset_erase.mp hT).1
    have hInsE : insert a T ⊆ E := Finset.insert_subset haE hTsub
    have hInsBL : insert a T ∩ L = U ∩ L := rc44_inter_insert T L U a haU hTtrace
    have hInsB : insert a T ∈ ℬ := hLB (insert a T) hInsE hInsBL
    rw [rc44_mem_slab1]
    exact ⟨insert a T, hInsB, Finset.mem_insert_self a T, Finset.erase_insert haT⟩








omit [Fintype α] in

theorem rc44_sdiff_erase_of_not_mem (E R : Finset α) (a : α) :
    (E.erase a) \ R = (E \ R).erase a := by
  ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hxa, hxE⟩, hxR⟩; exact ⟨hxa, hxE, hxR⟩
  · rintro ⟨hxa, hxE, hxR⟩; exact ⟨⟨hxa, hxE⟩, hxR⟩

omit [Fintype α] in

theorem rc44_sdiff_erase_of_mem (E R : Finset α) (a : α) (haR : a ∈ R) :
    (E.erase a) \ (R.erase a) = E \ R := by
  ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hxa, hxE⟩, hxR⟩; exact ⟨hxE, fun h => hxR ⟨hxa, h⟩⟩
  · rintro ⟨hxE, hxR⟩
    have hxa : x ≠ a := fun h => hxR (h ▸ haR)
    exact ⟨⟨hxa, hxE⟩, fun h => hxR h.2⟩

open Classical in




theorem rc44_reflInterE_slab0_card (E : Finset α) (a : α) (haE : a ∈ E)
    (𝒜 ℬ : Finset (Finset α)) :
    ((rc44_reflInterE E 𝒜 ℬ).filter (fun R => a ∉ R)).card
      = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card := by
  apply Finset.card_bij (fun R _ => R)
  · 
    intro R hR
    rw [Finset.mem_filter, rc44_mem_reflInterE] at hR
    obtain ⟨⟨hRE, hRA, hcB⟩, haR⟩ := hR
    rw [rc44_mem_reflInterE]
    refine ⟨Finset.subset_erase.mpr ⟨hRE, haR⟩, ?_, ?_⟩
    · rw [rc44_mem_slab0]; exact ⟨hRA, haR⟩
    · rw [rc44_sdiff_erase_of_not_mem, rc44_mem_slab1]
      exact ⟨E \ R, hcB, Finset.mem_sdiff.mpr ⟨haE, haR⟩, rfl⟩
  · 
    intro R _ R' _ h; exact h
  · 
    intro R hR
    rw [rc44_mem_reflInterE] at hR
    obtain ⟨hRsub, hRA0, hcB1⟩ := hR
    rw [rc44_mem_slab0] at hRA0
    have haR : a ∉ R := hRA0.2
    refine ⟨R, ?_, rfl⟩
    rw [Finset.mem_filter, rc44_mem_reflInterE]
    refine ⟨⟨hRsub.trans (Finset.erase_subset a E), hRA0.1, ?_⟩, haR⟩
    
    rw [rc44_mem_slab1] at hcB1
    obtain ⟨V, hVB, haV, hVeq⟩ := hcB1
    
    rw [rc44_sdiff_erase_of_not_mem] at hVeq
    have hVER : V = E \ R := by
      have haER : a ∈ E \ R := Finset.mem_sdiff.mpr ⟨haE, haR⟩
      rw [← Finset.insert_erase haV, ← Finset.insert_erase haER, hVeq]
    rw [← hVER]; exact hVB

open Classical in




theorem rc44_reflInterE_slab1_card (E : Finset α) (a : α) (haE : a ∈ E)
    (𝒜 ℬ : Finset (Finset α)) :
    ((rc44_reflInterE E 𝒜 ℬ).filter (fun R => a ∈ R)).card
      = (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card := by
  apply Finset.card_bij (fun R _ => R.erase a)
  · 
    intro R hR
    rw [Finset.mem_filter, rc44_mem_reflInterE] at hR
    obtain ⟨⟨hRE, hRA, hcB⟩, haR⟩ := hR
    rw [rc44_mem_reflInterE]
    refine ⟨Finset.erase_subset_erase a hRE, ?_, ?_⟩
    · rw [rc44_mem_slab1]; exact ⟨R, hRA, haR, rfl⟩
    · rw [rc44_sdiff_erase_of_mem E R a haR, rc44_mem_slab0]
      exact ⟨hcB, fun h => (Finset.mem_sdiff.mp h).2 haR⟩
  · 
    intro R hR R' hR' h
    rw [Finset.mem_filter] at hR hR'
    have haR : a ∈ R := hR.2
    have haR' : a ∈ R' := hR'.2
    rw [← Finset.insert_erase haR, ← Finset.insert_erase haR', h]
  · 
    intro Q hQ
    rw [rc44_mem_reflInterE] at hQ
    obtain ⟨hQsub, hQA1, hcB0⟩ := hQ
    rw [rc44_mem_slab1] at hQA1
    obtain ⟨R, hRA, haR, hReq⟩ := hQA1
    refine ⟨R, ?_, hReq⟩
    rw [Finset.mem_filter, rc44_mem_reflInterE]
    have hRE : R ⊆ E := by
      rw [← Finset.insert_erase haR, hReq, Finset.insert_subset_iff]
      exact ⟨haE, hQsub.trans (Finset.erase_subset a E)⟩
    refine ⟨⟨hRE, hRA, ?_⟩, haR⟩
    rw [rc44_mem_slab0] at hcB0
    rw [← rc44_sdiff_erase_of_mem E R a haR, hReq]
    exact hcB0.1

open Classical in










theorem rc44_reflInterE_card_recursion (E : Finset α) (a : α) (haE : a ∈ E)
    (𝒜 ℬ : Finset (Finset α)) :
    (rc44_reflInterE E 𝒜 ℬ).card
      = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card
        + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card := by
  rw [← rc44_reflInterE_slab0_card E a haE 𝒜 ℬ, ← rc44_reflInterE_slab1_card E a haE 𝒜 ℬ]
  rw [add_comm]
  exact (Finset.card_filter_add_card_filter_not (fun R => a ∈ R)).symm









def rc44_famCylBoxEComp (E : Finset α) (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  E.powerset.filter (fun S =>
    ((E.powerset ×ˢ E.powerset).filter (fun p => Disjoint p.1 p.2 ∧
      (∀ T ∈ E.powerset, T ∩ p.1 = S ∩ p.1 → T ∈ 𝒜) ∧
      (∀ T ∈ E.powerset, T ∩ p.2 = S ∩ p.2 → T ∈ ℬ))).Nonempty)


def rc44_reflInterEComp (E : Finset α) (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  E.powerset.filter (fun R => R ∈ 𝒜 ∧ E \ R ∈ ℬ)

open Classical in

theorem rc44_famCylBoxEComp_eq (E : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    rc44_famCylBoxEComp E 𝒜 ℬ = rc44_famCylBoxE E 𝒜 ℬ := by
  ext S
  rw [rc44_famCylBoxEComp, Finset.mem_filter, Finset.mem_powerset, rc44_mem_famCylBoxE]
  refine and_congr_right (fun hSE => ?_)
  constructor
  · rintro ⟨p, hp⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    obtain ⟨⟨hKE, hLE⟩, hKL, hKA, hLB⟩ := hp
    exact ⟨p.1, p.2, hKE, hLE, hKL,
      fun T hT => hKA T (Finset.mem_powerset.mpr hT),
      fun T hT => hLB T (Finset.mem_powerset.mpr hT)⟩
  · rintro ⟨K, L, hKE, hLE, hKL, hKA, hLB⟩
    refine ⟨(K, L), ?_⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨⟨hKE, hLE⟩, hKL, fun T hT => hKA T (Finset.mem_powerset.mp hT),
      fun T hT => hLB T (Finset.mem_powerset.mp hT)⟩

open Classical in

theorem rc44_reflInterEComp_eq (E : Finset α) (𝒜 ℬ : Finset (Finset α)) :
    rc44_reflInterEComp E 𝒜 ℬ = rc44_reflInterE E 𝒜 ℬ := by
  rfl
















def rc44_Aref : Finset (Finset (Fin 3)) := {∅, {1}, {1, 2}, {2}}


def rc44_Bref : Finset (Finset (Fin 3)) := {{0, 1}, {1}}















theorem rc44_diagonalSlab_charge_fails_fin3 :
    ({1} : Finset (Fin 3)) ∈ rc44_famCylBoxEComp {0, 1}
        (rc44_slab0 2 rc44_Aref) (rc44_slab0 2 rc44_Bref)
      ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1}
          (rc44_slab0 2 rc44_Aref) (rc44_slab1 2 rc44_Bref)
      ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1}
          (rc44_slab1 2 rc44_Aref) (rc44_slab0 2 rc44_Bref) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rc44_Aref, rc44_Bref, rc44_slab0, rc44_slab0]; decide
  · rw [rc44_Aref, rc44_Bref, rc44_slab0, rc44_slab1]; decide
  · rw [rc44_Aref, rc44_Bref, rc44_slab1, rc44_slab0]; decide











def rc44_BoxMonoResidue : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ)

open Classical in



theorem rc44_boxMonoResidue_iff_famCylBoxResidue :
    rc44_BoxMonoResidue ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    have := h n 𝒜 ℬ
    rwa [rc44_famCylBoxE_univ, rc44_reflInterE_univ] at this
  · intro h n 𝒜 ℬ
    have := h n 𝒜 ℬ
    rwa [rc44_famCylBoxE_univ, rc44_reflInterE_univ]

open Classical in



theorem rc44_reimer_closes_of_boxMonoResidue (h : rc44_BoxMonoResidue) :
    rc18_CylBoxReflInter :=
  rc20_famCylBoxResidue_iff_cylBoxReflInter.mp (rc44_boxMonoResidue_iff_famCylBoxResidue.mp h)







open Classical in



theorem rc44_boxMonoResidue_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) := by
  rw [rc44_famCylBoxE_univ, rc44_reflInterE_univ]
  exact rc20_famCylBox_fin2 𝒜 ℬ



set_option linter.unusedVariables false in
open Classical in










































theorem rc44_reimer_coordinate_induction :
    (rc44_BoxMonoResidue ↔ rc20_FamCylBoxResidue)
      ∧ (rc44_BoxMonoResidue → rc18_CylBoxReflInter)
      ∧ (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)),
          rc44_slab0 a (rc44_famCylBoxE E 𝒜 ℬ)
            ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ))
      ∧ (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)),
          rc44_slab1 a (rc44_famCylBoxE E 𝒜 ℬ)
            ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ))
      ∧ (∀ (E : Finset α) (a : α), a ∈ E → ∀ (𝒜 ℬ : Finset (Finset α)),
          (rc44_reflInterE E 𝒜 ℬ).card
            = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card
              + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card)
      ∧ (({1} : Finset (Fin 3)) ∈ rc44_famCylBoxEComp {0, 1}
            (rc44_slab0 2 rc44_Aref) (rc44_slab0 2 rc44_Bref)
          ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1}
              (rc44_slab0 2 rc44_Aref) (rc44_slab1 2 rc44_Bref)
          ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1}
              (rc44_slab1 2 rc44_Aref) (rc44_slab0 2 rc44_Bref)) :=
  ⟨rc44_boxMonoResidue_iff_famCylBoxResidue,
    rc44_reimer_closes_of_boxMonoResidue,
    fun E a 𝒜 ℬ => rc44_slab0_famCylBoxE_subset E a 𝒜 ℬ,
    fun E a 𝒜 ℬ => rc44_slab1_famCylBoxE_subset E a 𝒜 ℬ,
    fun E a haE 𝒜 ℬ => rc44_reflInterE_card_recursion E a haE 𝒜 ℬ,
    rc44_diagonalSlab_charge_fails_fin3⟩

end StatMech.Walls
