/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Code.Walls.rc81shifttomonotone

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









def rc82_pushDown (i : ι) (w : ConfigSpace ι) : ConfigSpace ι := Function.update w i false

def rc82_pushUp (i : ι) (w : ConfigSpace ι) : ConfigSpace ι := Function.update w i true



def rc82_downMap (i : ι) (A : Finset (ConfigSpace ι)) (w : ConfigSpace ι) : ConfigSpace ι :=
  if w i = true ∧ rc82_pushDown i w ∉ A then rc82_pushDown i w else w



def rc82_upMap (i : ι) (B : Finset (ConfigSpace ι)) (w : ConfigSpace ι) : ConfigSpace ι :=
  if w i = false ∧ rc82_pushUp i w ∉ B then rc82_pushUp i w else w


def rc82_downCompressA (i : ι) (A : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  A.image (rc82_downMap i A)


def rc82_upCompressB (i : ι) (B : Finset (ConfigSpace ι)) : Finset (ConfigSpace ι) :=
  B.image (rc82_upMap i B)







theorem rc82_downMap_injOn (i : ι) (A : Finset (ConfigSpace ι)) :
    Set.InjOn (rc82_downMap i A) A := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  unfold rc82_downMap at hab
  by_cases hA : a i = true ∧ rc82_pushDown i a ∉ A
  · rw [if_pos hA] at hab
    by_cases hB : b i = true ∧ rc82_pushDown i b ∉ A
    · rw [if_pos hB] at hab
      
      have : a = b := by
        funext j
        by_cases hj : j = i
        · subst hj; rw [hA.1, hB.1]
        · have := congrFun hab j
          simp only [rc82_pushDown, Function.update_of_ne hj] at this
          exact this
      exact this
    · rw [if_neg hB] at hab
      
      rw [← hab] at hb
      exact absurd hb hA.2
  · rw [if_neg hA] at hab
    by_cases hB : b i = true ∧ rc82_pushDown i b ∉ A
    · rw [if_pos hB] at hab
      
      rw [hab] at ha
      exact absurd ha hB.2
    · rw [if_neg hB] at hab; exact hab


theorem rc82_upMap_injOn (i : ι) (B : Finset (ConfigSpace ι)) :
    Set.InjOn (rc82_upMap i B) B := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  unfold rc82_upMap at hab
  by_cases hA : a i = false ∧ rc82_pushUp i a ∉ B
  · rw [if_pos hA] at hab
    by_cases hB : b i = false ∧ rc82_pushUp i b ∉ B
    · rw [if_pos hB] at hab
      have : a = b := by
        funext j
        by_cases hj : j = i
        · subst hj; rw [hA.1, hB.1]
        · have := congrFun hab j
          simp only [rc82_pushUp, Function.update_of_ne hj] at this
          exact this
      exact this
    · rw [if_neg hB] at hab
      rw [← hab] at hb
      exact absurd hb hA.2
  · rw [if_neg hA] at hab
    by_cases hB : b i = false ∧ rc82_pushUp i b ∉ B
    · rw [if_pos hB] at hab
      rw [hab] at ha
      exact absurd ha hB.2
    · rw [if_neg hB] at hab; exact hab



theorem rc82_downCompressA_card (i : ι) (A : Finset (ConfigSpace ι)) :
    (rc82_downCompressA i A).card = A.card :=
  Finset.card_image_of_injOn (rc82_downMap_injOn i A)


theorem rc82_upCompressB_card (i : ι) (B : Finset (ConfigSpace ι)) :
    (rc82_upCompressB i B).card = B.card :=
  Finset.card_image_of_injOn (rc82_upMap_injOn i B)













theorem rc82_occ_lower_iff {A : Finset (ConfigSpace ι)} (hA : rc80_IsLower A)
    (K : Finset ι) (w : ConfigSpace ι) :
    rc80_occ A K w = true ↔ rc80_maxext K w ∈ A := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  constructor
  · intro h
    exact h (rc80_maxext K w) (fun e he => rc80_maxext_agree K w he)
  · intro hmax w' hw'
    
    refine rc80_lower_mono hA ?_ hmax
    intro i hi
    by_cases hiK : i ∈ K
    · rw [rc80_maxext_agree K w hiK]; rw [hw' i hiK] at hi; exact hi
    · simp only [rc80_maxext, hiK, if_false]


theorem rc82_occ_upper_iff {B : Finset (ConfigSpace ι)} (hB : rc80_IsUpper B)
    (L : Finset ι) (w : ConfigSpace ι) :
    rc80_occ B L w = true ↔ rc80_minext L w ∈ B := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  constructor
  · intro h
    exact h (rc80_minext L w) (fun e he => rc80_minext_agree L w he)
  · intro hmin w' hw'
    
    refine rc80_upper_mono hB ?_ hmin
    intro i hi
    by_cases hiL : i ∈ L
    · rw [rc80_minext_agree L w hiL] at hi; rw [hw' i hiL]; exact hi
    · simp only [rc80_minext, hiL, if_false] at hi; exact absurd hi (by simp)








theorem rc82_disjOccG_eq_inter_of_lower_upper {A B : Finset (ConfigSpace ι)}
    (hA : rc80_IsLower A) (hB : rc80_IsUpper B) :
    rc80_disjOccG A B = A ∩ B := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨K, L, _, hK, hL⟩
    rw [rc82_occ_lower_iff hA] at hK
    rw [rc82_occ_upper_iff hB] at hL
    refine ⟨?_, ?_⟩
    · 
      refine rc80_lower_mono hA (fun i hi => rc80_le_maxext K w i hi) hK
    · 
      refine rc80_upper_mono hB (fun i hi => rc80_minext_le L w i hi) hL
  · rintro ⟨hwA, hwB⟩
    refine ⟨Finset.univ.filter (fun i => w i = false), Finset.univ.filter (fun i => w i = true),
      ?_, ?_, ?_⟩
    · 
      rw [Finset.disjoint_filter]
      intro i _ hi
      simp only [hi, Bool.false_eq_true, not_false_eq_true]
    · 
      rw [rc82_occ_lower_iff hA]
      have : rc80_maxext (Finset.univ.filter (fun i => w i = false)) w = w := by
        funext i
        simp only [rc80_maxext, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hw : w i <;> simp
      rw [this]; exact hwA
    · 
      rw [rc82_occ_upper_iff hB]
      have : rc80_minext (Finset.univ.filter (fun i => w i = true)) w = w := by
        funext i
        simp only [rc80_minext, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hw : w i <;> simp
      rw [this]; exact hwB




theorem rc82_wall_lower_upper_iff {A B : Finset (ConfigSpace ι)}
    (hA : rc80_IsLower A) (hB : rc80_IsUpper B) :
    (rc80_disjOccG A B).card ≤ (rc80_reflInterG A B).card
      ↔ (A ∩ B).card ≤ (rc80_reflInterG A B).card := by
  rw [rc82_disjOccG_eq_inter_of_lower_upper hA hB]









set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 





theorem rc82_wall_holds_everywhere_fin2 :
    ∀ A B : Finset (ConfigSpace (Fin 2)),
      (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card := by
  decide










def rc82_topF : ConfigSpace (Fin 2) := fun _ => true


def rc82_wA : Finset (ConfigSpace (Fin 2)) := {rc82_topF}



theorem rc82_reflInter_orig_zero : (rc80_reflInterG rc82_wA rc82_wA).card = 0 := by decide


theorem rc82_downClosure_wA_univ :
    rc81_downClosure rc82_wA = (Finset.univ : Finset (ConfigSpace (Fin 2))) := by decide



theorem rc82_reflInter_shifted_one :
    (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card = 1 := by decide






theorem rc82_downup_shift_refutes_wall_witness :
    (rc80_reflInterG rc82_wA rc82_wA).card
      < (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card := by
  rw [rc82_reflInter_orig_zero, rc82_reflInter_shifted_one]; exact Nat.zero_lt_one





theorem rc82_lowerWitness : rc80_IsLower ({rc81_botF} : Finset (ConfigSpace (Fin 2))) :=
  rc80_monoWitness_lower

theorem rc82_upperWitness : rc80_IsUpper ({rc82_topF} : Finset (ConfigSpace (Fin 2))) :=
  rc80_monoWitness_upper


theorem rc82_dualWitness_reduces :
    rc80_disjOccG ({rc81_botF} : Finset (ConfigSpace (Fin 2))) {rc82_topF}
      = ({rc81_botF} : Finset (ConfigSpace (Fin 2))) ∩ {rc82_topF} :=
  rc82_disjOccG_eq_inter_of_lower_upper rc82_lowerWitness rc82_upperWitness

open Classical in



theorem rc82_reimerWprobCore_of_boxUnionBound (h : rc60_BoxUnionBound) : ReimerWprobCore :=
  rc81_reimerWprobCore_of_boxUnionBound h

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in 





























theorem rc82_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (A : Finset (ConfigSpace ι)),
        (rc82_downCompressA i A).card = A.card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (B : Finset (ConfigSpace ι)),
        (rc82_upCompressB i B).card = B.card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧
    
    ((rc80_reflInterG rc82_wA rc82_wA).card
        < (rc80_reflInterG (rc81_downClosure rc82_wA) rc82_wA).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun i A => rc82_downCompressA_card i A,
   fun i B => rc82_upCompressB_card i B,
   fun _ _ hA hB => rc82_disjOccG_eq_inter_of_lower_upper hA hB,
   rc82_wall_holds_everywhere_fin2,
   rc82_downup_shift_refutes_wall_witness,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
