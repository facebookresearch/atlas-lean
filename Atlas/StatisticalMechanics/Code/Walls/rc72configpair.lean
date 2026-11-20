/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Code.Walls.rc71disjpreserving
import Code.Inequalities.DisjointOccurrence

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}











def graftSwap (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    ConfigSpace (Fin n) × ConfigSpace (Fin n) :=
  (fun i => if i ∈ L then p.2 i else p.1 i,
   fun i => if i ∈ L then p.1 i else p.2 i)




theorem graftSwap_involutive (L : Finset (Fin n)) :
    Function.Involutive (graftSwap L) := by
  intro p
  unfold graftSwap
  ext i <;> simp only [] <;> split_ifs <;> rfl




theorem graftSwap_bijective (L : Finset (Fin n)) :
    Function.Bijective (graftSwap L) :=
  (graftSwap_involutive L).bijective



theorem graftSwap_fst_off (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n))
    {i : Fin n} (hi : i ∉ L) : (graftSwap L p).1 i = p.1 i := by
  simp only [graftSwap, hi, if_false]



theorem graftSwap_snd_on (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n))
    {i : Fin n} (hi : i ∈ L) : (graftSwap L p).2 i = p.1 i := by
  simp only [graftSwap, hi, if_true]



















theorem graftSwap_mapsInto_of_witness (A B : Set (ConfigSpace (Fin n)))
    {K L : Finset (Fin n)} (hKL : Disjoint K L) (ω₁ ω₂ : ConfigSpace (Fin n))
    (hA : OccursOn A (K : Set (Fin n)) ω₁) (hB : OccursOn B (L : Set (Fin n)) ω₁) :
    (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B := by
  refine ⟨?_, ?_⟩
  · 
    apply hA
    intro e he
    have heL : e ∉ L := fun heL => (Finset.disjoint_left.mp hKL he) heL
    exact graftSwap_fst_off L (ω₁, ω₂) heL
  · 
    apply hB
    intro e he
    exact graftSwap_snd_on L (ω₁, ω₂) he
















theorem graftSwap_pair_perm (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n))
    (i : Fin n) :
    ((graftSwap L p).1 i, (graftSwap L p).2 i) = (p.1 i, p.2 i)
      ∨ ((graftSwap L p).1 i, (graftSwap L p).2 i) = (p.2 i, p.1 i) := by
  by_cases hi : i ∈ L
  · right; simp only [graftSwap, hi, if_true]
  · left; simp only [graftSwap, hi, if_false]








theorem graftSwap_jointCount (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    (Finset.univ.filter (fun i => (graftSwap L p).1 i = true)).card
        + (Finset.univ.filter (fun i => (graftSwap L p).2 i = true)).card
      = (Finset.univ.filter (fun i => p.1 i = true)).card
        + (Finset.univ.filter (fun i => p.2 i = true)).card := by
  
  rw [← Finset.card_union_add_card_inter, ← Finset.card_union_add_card_inter]
  
  have key : ∀ i : Fin n,
      (if (graftSwap L p).1 i = true then 1 else 0) + (if (graftSwap L p).2 i = true then 1 else 0)
        = (if p.1 i = true then 1 else 0) + (if p.2 i = true then 1 else 0) := by
    intro i
    rcases graftSwap_pair_perm L p i with h | h
    · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]
    · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]; ring
  
  have card_as_sum : ∀ (q : ConfigSpace (Fin n)),
      (Finset.univ.filter (fun i => q i = true)).card
        = ∑ i : Fin n, (if q i = true then 1 else 0) := by
    intro q
    rw [Finset.card_filter]
  rw [Finset.card_union_add_card_inter, Finset.card_union_add_card_inter,
    card_as_sum, card_as_sum, card_as_sum, card_as_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => key i)


















def rc72_occ (A : Finset (ConfigSpace (Fin 2))) (K : Finset (Fin 2)) (ω : ConfigSpace (Fin 2)) :
    Bool :=
  decide (∀ ω' : ConfigSpace (Fin 2), (∀ e ∈ K, ω' e = ω e) → ω' ∈ A)



def rc72_disjOcc (A B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  Finset.univ.filter (fun ω =>
    ∃ K L : Finset (Fin 2), Disjoint K L ∧ rc72_occ A K ω = true ∧ rc72_occ B L ω = true)




def rc72_wits (A B : Finset (ConfigSpace (Fin 2))) (ω : ConfigSpace (Fin 2)) :
    Finset (Finset (Fin 2)) :=
  (Finset.univ : Finset (Finset (Fin 2))).filter (fun L =>
    ∃ K : Finset (Fin 2), Disjoint K L ∧ rc72_occ A K ω = true ∧ rc72_occ B L ω = true)





def rc72_reachCells (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  ((rc72_disjOcc A B).biUnion (fun ω₁ =>
    (Finset.univ : Finset (ConfigSpace (Fin 2))).biUnion (fun ω₂ =>
      (rc72_wits A B ω₁).image (fun L => graftSwap L (ω₁, ω₂))))).filter
    (fun u => u.1 ∈ A ∧ u.2 ∈ B)



def rc72_cfg (b0 b1 : Bool) : ConfigSpace (Fin 2) := fun i => if i = 0 then b0 else b1


def rc72_wA : Finset (ConfigSpace (Fin 2)) :=
  {rc72_cfg false false, rc72_cfg true false, rc72_cfg false true}


def rc72_wB : Finset (ConfigSpace (Fin 2)) :=
  {rc72_cfg false false, rc72_cfg true false, rc72_cfg true true}

set_option maxRecDepth 8000 in





theorem rc72_witness_counts :
    (rc72_disjOcc rc72_wA rc72_wB).card = 2
    ∧ rc72_wA.card * rc72_wB.card = 9
    ∧ (rc72_reachCells rc72_wA rc72_wB).card = 7 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 8000 in











theorem rc72_graftSwap_reach_cap_fin2 :
    (rc72_reachCells rc72_wA rc72_wB).card
      < 2 ^ 2 * (rc72_disjOcc rc72_wA rc72_wB).card := by
  decide














def rc72_source (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  (rc72_disjOcc A B) ×ˢ (Finset.univ : Finset (ConfigSpace (Fin 2)))



theorem rc72_source_card (A B : Finset (ConfigSpace (Fin 2))) :
    (rc72_source A B).card = (rc72_disjOcc A B).card * 2 ^ 2 := by
  rw [rc72_source, Finset.card_product, Finset.card_univ]
  congr 1




theorem rc72_graftSwap_mem_reachCells (A B : Finset (ConfigSpace (Fin 2)))
    {ω₁ ω₂ : ConfigSpace (Fin 2)} (hω₁ : ω₁ ∈ rc72_disjOcc A B)
    {L : Finset (Fin 2)} (hL : L ∈ rc72_wits A B ω₁)
    (hAB : (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B) :
    graftSwap L (ω₁, ω₂) ∈ rc72_reachCells A B := by
  rw [rc72_reachCells, Finset.mem_filter]
  refine ⟨?_, hAB⟩
  rw [Finset.mem_biUnion]
  exact ⟨ω₁, hω₁, Finset.mem_biUnion.mpr ⟨ω₂, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨L, hL, rfl⟩⟩⟩

open Classical in











theorem rc72_source_card_le_reach_of_injection (A B : Finset (ConfigSpace (Fin 2)))
    (Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2))
    (hwit : ∀ ω₁ ∈ rc72_disjOcc A B, ∀ ω₂ : ConfigSpace (Fin 2), Lc ω₁ ω₂ ∈ rc72_wits A B ω₁)
    (hAB : ∀ ω₁ ∈ rc72_disjOcc A B, ∀ ω₂ : ConfigSpace (Fin 2),
        (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ A ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ B)
    (hinj : Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) =>
        graftSwap (Lc p.1 p.2) p) (rc72_source A B)) :
    2 ^ 2 * (rc72_disjOcc A B).card ≤ (rc72_reachCells A B).card := by
  
  have hmaps : ∀ p ∈ rc72_source A B,
      (fun q : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) => graftSwap (Lc q.1 q.2) q) p
        ∈ rc72_reachCells A B := by
    rintro ⟨ω₁, ω₂⟩ hp
    rw [rc72_source, Finset.mem_product] at hp
    obtain ⟨hω₁, _⟩ := hp
    exact rc72_graftSwap_mem_reachCells A B hω₁ (hwit ω₁ hω₁ ω₂) (hAB ω₁ hω₁ ω₂)
  have := Finset.card_le_card_of_injOn
    (f := fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) => graftSwap (Lc p.1 p.2) p)
    hmaps hinj
  rwa [rc72_source_card, mul_comm] at this

open Classical in
set_option maxRecDepth 8000 in







theorem rc72_no_graftSwap_injection_fin2 :
    ¬ ∃ Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2),
        (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2),
            Lc ω₁ ω₂ ∈ rc72_wits rc72_wA rc72_wB ω₁) ∧
        (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2),
            (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ rc72_wA
              ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ rc72_wB) ∧
        Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) =>
            graftSwap (Lc p.1 p.2) p) (rc72_source rc72_wA rc72_wB) := by
  rintro ⟨Lc, hwit, hAB, hinj⟩
  have hbound := rc72_source_card_le_reach_of_injection rc72_wA rc72_wB Lc hwit hAB hinj
  obtain ⟨hdisj, _, hreach⟩ := rc72_witness_counts
  rw [hdisj, hreach] at hbound
  
  omega



open Classical in




theorem rc72_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc71_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 8000 in

































theorem rc72_status :
    
    (∀ (m : ℕ) (L : Finset (Fin m)), Function.Bijective (graftSwap L)) ∧
    (∀ (m : ℕ) (L : Finset (Fin m)) (p : ConfigSpace (Fin m) × ConfigSpace (Fin m)),
        (Finset.univ.filter (fun i => (graftSwap L p).1 i = true)).card
            + (Finset.univ.filter (fun i => (graftSwap L p).2 i = true)).card
          = (Finset.univ.filter (fun i => p.1 i = true)).card
            + (Finset.univ.filter (fun i => p.2 i = true)).card) ∧
    
    (∀ (m : ℕ) (A B : Set (ConfigSpace (Fin m))) (K L : Finset (Fin m)), Disjoint K L →
        ∀ (ω₁ ω₂ : ConfigSpace (Fin m)),
        OccursOn A (K : Set (Fin m)) ω₁ → OccursOn B (L : Set (Fin m)) ω₁ →
        (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B) ∧
    
    ((rc72_reachCells rc72_wA rc72_wB).card
        < 2 ^ 2 * (rc72_disjOcc rc72_wA rc72_wB).card) ∧
    
    (¬ ∃ Lc : ConfigSpace (Fin 2) → ConfigSpace (Fin 2) → Finset (Fin 2),
        (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2),
            Lc ω₁ ω₂ ∈ rc72_wits rc72_wA rc72_wB ω₁) ∧
        (∀ ω₁ ∈ rc72_disjOcc rc72_wA rc72_wB, ∀ ω₂ : ConfigSpace (Fin 2),
            (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).1 ∈ rc72_wA
              ∧ (graftSwap (Lc ω₁ ω₂) (ω₁, ω₂)).2 ∈ rc72_wB) ∧
        Set.InjOn (fun p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) =>
            graftSwap (Lc p.1 p.2) p) (rc72_source rc72_wA rc72_wB)) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _m L => graftSwap_bijective L,
   fun _m L p => graftSwap_jointCount L p,
   fun _m A B _K _L hKL ω₁ ω₂ hA hB => graftSwap_mapsInto_of_witness A B hKL ω₁ ω₂ hA hB,
   rc72_graftSwap_reach_cap_fin2,
   rc72_no_graftSwap_injection_fin2,
   rc72_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
