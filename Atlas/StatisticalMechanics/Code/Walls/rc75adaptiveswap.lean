/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Code.Walls.rc74doubledwall

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}













def swapAt (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    ConfigSpace (Fin n) × ConfigSpace (Fin n) :=
  (fun j => if j = i then p.2 i else p.1 j, fun j => if j = i then p.1 i else p.2 j)


theorem swapAt_involutive (i : Fin n) : Function.Involutive (swapAt i) := by
  intro p
  unfold swapAt
  ext j <;> simp only [] <;> split_ifs with h <;> subst_vars <;> rfl



theorem swapAt_bijective (i : Fin n) : Function.Bijective (swapAt i) :=
  (swapAt_involutive i).bijective


theorem swapAt_off (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) {j : Fin n}
    (hj : j ≠ i) : (swapAt i p).1 j = p.1 j ∧ (swapAt i p).2 j = p.2 j := by
  refine ⟨?_, ?_⟩ <;> simp only [swapAt, if_neg hj]


theorem swapAt_on (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    (swapAt i p).1 i = p.2 i ∧ (swapAt i p).2 i = p.1 i := by
  refine ⟨?_, ?_⟩ <;> simp only [swapAt, if_pos]






theorem swapAt_pair_perm (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) (j : Fin n) :
    ((swapAt i p).1 j, (swapAt i p).2 j) = (p.1 j, p.2 j)
      ∨ ((swapAt i p).1 j, (swapAt i p).2 j) = (p.2 j, p.1 j) := by
  by_cases hj : j = i
  · right; subst hj; simp only [swapAt, if_pos]
  · left; simp only [swapAt, if_neg hj]





def coordSwap (i : Fin n) (pred : ConfigSpace (Fin n) × ConfigSpace (Fin n) → Prop)
    [DecidablePred pred] (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    ConfigSpace (Fin n) × ConfigSpace (Fin n) :=
  if pred p then swapAt i p else p




theorem coordSwap_involutive (i : Fin n) (pred : ConfigSpace (Fin n) × ConfigSpace (Fin n) → Prop)
    [DecidablePred pred] (horb : ∀ p, pred (swapAt i p) ↔ pred p) :
    Function.Involutive (coordSwap i pred) := by
  intro p
  unfold coordSwap
  by_cases h : pred p
  · rw [if_pos h]
    have h2 : pred (swapAt i p) := (horb p).mpr h
    rw [if_pos h2, swapAt_involutive i p]
  · rw [if_neg h, if_neg h]


theorem coordSwap_bijective (i : Fin n) (pred : ConfigSpace (Fin n) × ConfigSpace (Fin n) → Prop)
    [DecidablePred pred] (horb : ∀ p, pred (swapAt i p) ↔ pred p) :
    Function.Bijective (coordSwap i pred) :=
  (coordSwap_involutive i pred horb).bijective














theorem swapAt_mapsInto_of_witness (A B : Set (ConfigSpace (Fin n)))
    {K : Finset (Fin n)} {i : Fin n} (hKi : Disjoint K {i}) (ω₁ ω₂ : ConfigSpace (Fin n))
    (hA : OccursOn A (K : Set (Fin n)) ω₁) (hB : OccursOn B ({i} : Finset (Fin n)) ω₁) :
    (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B := by
  refine ⟨?_, ?_⟩
  · apply hA
    intro e he
    have hei : e ≠ i := by
      intro h; subst h
      exact (Finset.disjoint_left.mp hKi he) (Finset.mem_singleton_self _)
    exact (swapAt_off i (ω₁, ω₂) hei).1
  · apply hB
    intro e he
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at he
    rw [he]
    exact (swapAt_on i (ω₁, ω₂)).2















def rc75_swapAtF (i : Fin 2) (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  (fun j => if j = i then p.2 i else p.1 j, fun j => if j = i then p.1 i else p.2 j)


theorem rc75_swapAtF_involutive (i : Fin 2) : Function.Involutive (rc75_swapAtF i) := by
  intro p
  unfold rc75_swapAtF
  ext j <;> simp only [] <;> split_ifs with h <;> subst_vars <;> rfl




def rc75_orbSwap (i : Fin 2) (c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)))
    (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) :=
  if (p ∈ c ∨ rc75_swapAtF i p ∈ c) then rc75_swapAtF i p else p




theorem rc75_orbSwap_involutive (i : Fin 2) (c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))) :
    Function.Involutive (rc75_orbSwap i c) := by
  intro p
  unfold rc75_orbSwap
  by_cases h : p ∈ c ∨ rc75_swapAtF i p ∈ c
  · rw [if_pos h]
    have h2 : rc75_swapAtF i p ∈ c ∨ rc75_swapAtF i (rc75_swapAtF i p) ∈ c := by
      rw [rc75_swapAtF_involutive i p]; tauto
    rw [if_pos h2, rc75_swapAtF_involutive i p]
  · rw [if_neg h, if_neg h]


theorem rc75_orbSwap_bijective (i : Fin 2) (c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))) :
    Function.Bijective (rc75_orbSwap i c) :=
  (rc75_orbSwap_involutive i c).bijective



def rc75_applyChoice (i : Fin 2) (c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)))
    (img : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  img.image (rc75_orbSwap i c)







theorem rc75_applyChoice_card (i : Fin 2) (c : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)))
    (img : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))) :
    (rc75_applyChoice i c img).card = img.card := by
  unfold rc75_applyChoice
  exact Finset.card_image_of_injective img (rc75_orbSwap_bijective i c).injective











def rc75_occ (A : Finset (ConfigSpace (Fin 2))) (K : Finset (Fin 2)) (ω : ConfigSpace (Fin 2)) : Bool :=
  decide (∀ ω' : ConfigSpace (Fin 2), (∀ e ∈ K, ω' e = ω e) → ω' ∈ A)


def rc75_disjOccF (A B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  Finset.univ.filter (fun ω =>
    ∃ K L : Finset (Fin 2), Disjoint K L ∧ rc75_occ A K ω = true ∧ rc75_occ B L ω = true)



def rc75_sourceF (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  (rc75_disjOccF A B) ×ˢ (Finset.univ : Finset (ConfigSpace (Fin 2)))


def rc75_prodF (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  A ×ˢ B



def rc75_orbReps (i : Fin 2) : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  Finset.univ.filter (fun p => p.1 i = true ∧ p.2 i = false)






def rc75_existsPlanOrder : List (Fin 2) → Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) →
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) → Prop
  | [], img, target => img ⊆ target
  | i :: rest, img, target =>
      ∃ c ∈ (rc75_orbReps i).powerset, rc75_existsPlanOrder rest (rc75_applyChoice i c img) target

instance rc75_decidableExistsPlanOrder :
    ∀ (o : List (Fin 2)) (img target : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))),
    Decidable (rc75_existsPlanOrder o img target)
  | [], _, _ => by unfold rc75_existsPlanOrder; infer_instance
  | i :: rest, img, target => by
      unfold rc75_existsPlanOrder
      have : ∀ c, Decidable (rc75_existsPlanOrder rest (rc75_applyChoice i c img) target) :=
        fun c => rc75_decidableExistsPlanOrder rest _ _
      infer_instance




def rc75_existsAdaptivePlan (A B : Finset (ConfigSpace (Fin 2))) : Prop :=
  rc75_existsPlanOrder [0, 1] (rc75_sourceF A B) (rc75_prodF A B) ∨
    rc75_existsPlanOrder [1, 0] (rc75_sourceF A B) (rc75_prodF A B)

instance (A B : Finset (ConfigSpace (Fin 2))) : Decidable (rc75_existsAdaptivePlan A B) := by
  unfold rc75_existsAdaptivePlan; infer_instance




def rc75_cfg (b0 b1 : Bool) : ConfigSpace (Fin 2) := fun i => if i = 0 then b0 else b1


def rc75_wA : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg true false, rc75_cfg false true}


def rc75_wB : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg true false, rc75_cfg true true}


def rc75_gA : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg false true, rc75_cfg true false}


def rc75_gB : Finset (ConfigSpace (Fin 2)) :=
  {rc75_cfg false false, rc75_cfg false true, rc75_cfg true true}




set_option maxRecDepth 8000 in









theorem rc75_adaptive_succeeds_where_rc72_failed :
    rc75_existsAdaptivePlan rc75_wA rc75_wB := by decide

set_option maxRecDepth 8000 in



theorem rc75_disjOcc_wit_card : (rc75_disjOccF rc75_wA rc75_wB).card = 2 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 







theorem rc75_adaptivePlan_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card → rc75_existsAdaptivePlan A B := by
  decide

set_option maxRecDepth 8000 in









theorem rc75_order_dependence :
    rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)
    ∧ ¬ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)
    ∧ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_gA rc75_gB) (rc75_prodF rc75_gA rc75_gB)
    ∧ ¬ rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_gA rc75_gB) (rc75_prodF rc75_gA rc75_gB) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide







def rc75_swapAtF1 (p : ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :
    ConfigSpace (Fin 1) × ConfigSpace (Fin 1) :=
  (fun j => if j = 0 then p.2 0 else p.1 j, fun j => if j = 0 then p.1 0 else p.2 j)


def rc75_applyChoice1 (c : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)))
    (img : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1))) :
    Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :=
  img.image (fun p => if (p ∈ c ∨ rc75_swapAtF1 p ∈ c) then rc75_swapAtF1 p else p)


def rc75_orbReps1 : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :=
  Finset.univ.filter (fun p => p.1 0 = true ∧ p.2 0 = false)


def rc75_occ1 (A : Finset (ConfigSpace (Fin 1))) (K : Finset (Fin 1)) (ω : ConfigSpace (Fin 1)) : Bool :=
  decide (∀ ω' : ConfigSpace (Fin 1), (∀ e ∈ K, ω' e = ω e) → ω' ∈ A)


def rc75_disjOccF1 (A B : Finset (ConfigSpace (Fin 1))) : Finset (ConfigSpace (Fin 1)) :=
  Finset.univ.filter (fun ω =>
    ∃ K L : Finset (Fin 1), Disjoint K L ∧ rc75_occ1 A K ω = true ∧ rc75_occ1 B L ω = true)


def rc75_sourceF1 (A B : Finset (ConfigSpace (Fin 1))) :
    Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :=
  (rc75_disjOccF1 A B) ×ˢ (Finset.univ : Finset (ConfigSpace (Fin 1)))


def rc75_prodF1 (A B : Finset (ConfigSpace (Fin 1))) :
    Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :=
  A ×ˢ B


def rc75_existsPlan1 (img target : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1))) : Prop :=
  ∃ c ∈ rc75_orbReps1.powerset, rc75_applyChoice1 c img ⊆ target

instance (img target : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1))) :
    Decidable (rc75_existsPlan1 img target) := by unfold rc75_existsPlan1; infer_instance

set_option maxRecDepth 8000 in




theorem rc75_adaptivePlan_fin1 :
    ∀ A B : Finset (ConfigSpace (Fin 1)),
      2 ^ 1 * (rc75_disjOccF1 A B).card ≤ A.card * B.card →
      rc75_existsPlan1 (rc75_sourceF1 A B) (rc75_prodF1 A B) := by
  decide



open Classical in





theorem rc75_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc74_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 


































theorem rc75_status :
    
    (∀ (i : Fin 2) (c img : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2))),
        (rc75_applyChoice i c img).card = img.card) ∧
    
    (∀ (m : ℕ) (i : Fin m) (pred : ConfigSpace (Fin m) × ConfigSpace (Fin m) → Prop)
        [DecidablePred pred], (∀ p, pred (swapAt i p) ↔ pred p) →
        Function.Bijective (coordSwap i pred)) ∧
    
    (∀ (m : ℕ) (A B : Set (ConfigSpace (Fin m))) (K : Finset (Fin m)) (i : Fin m),
        Disjoint K {i} → ∀ (ω₁ ω₂ : ConfigSpace (Fin m)),
        OccursOn A (K : Set (Fin m)) ω₁ → OccursOn B ({i} : Finset (Fin m)) ω₁ →
        (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        2 ^ 2 * (rc75_disjOccF A B).card ≤ A.card * B.card → rc75_existsAdaptivePlan A B) ∧
    
    rc75_existsAdaptivePlan rc75_wA rc75_wB ∧
    
    (rc75_existsPlanOrder [1, 0] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)
      ∧ ¬ rc75_existsPlanOrder [0, 1] (rc75_sourceF rc75_wA rc75_wB) (rc75_prodF rc75_wA rc75_wB)) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun i c img => rc75_applyChoice_card i c img,
   fun _m i pred _inst horb => coordSwap_bijective i pred horb,
   fun _m A B _K _i hKi ω₁ ω₂ hA hB => swapAt_mapsInto_of_witness A B hKi ω₁ ω₂ hA hB,
   rc75_adaptivePlan_fin2,
   rc75_adaptive_succeeds_where_rc72_failed,
   ⟨rc75_order_dependence.1, rc75_order_dependence.2.1⟩,
   rc75_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
