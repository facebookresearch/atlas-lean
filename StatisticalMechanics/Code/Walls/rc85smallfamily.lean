/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Code.Walls.rc82fixedordercompress

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem rc85_occ_empty (K : Finset ι) (w : ConfigSpace ι) :
    rc80_occ (∅ : Finset (ConfigSpace ι)) K w = false := by
  unfold rc80_occ
  rw [decide_eq_false_iff_not]
  intro h
  
  exact absurd (h w (fun _ _ => rfl)) (Finset.notMem_empty w)


theorem rc85_disjOccG_empty_left (B : Finset (ConfigSpace ι)) :
    rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B = ∅ := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_exists, not_and]
  intro K L _ hK _
  rw [rc85_occ_empty] at hK
  exact Bool.noConfusion hK


theorem rc85_disjOccG_empty_right (A : Finset (ConfigSpace ι)) :
    rc80_disjOccG A (∅ : Finset (ConfigSpace ι)) = ∅ := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_exists, not_and]
  intro K L _ _ hL
  rw [rc85_occ_empty] at hL
  exact Bool.noConfusion hL



theorem rc85_wall_empty_left (B : Finset (ConfigSpace ι)) :
    (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card := by
  rw [rc85_disjOccG_empty_left]; exact Nat.zero_le _


theorem rc85_wall_empty_right (A : Finset (ConfigSpace ι)) :
    (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card := by
  rw [rc85_disjOccG_empty_right]; exact Nat.zero_le _









theorem rc85_occ_singleton_iff (a : ConfigSpace ι) (K : Finset ι) (w : ConfigSpace ι) :
    rc80_occ ({a} : Finset (ConfigSpace ι)) K w = true ↔ K = Finset.univ ∧ w = a := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  constructor
  · intro h
    
    have hwa : w = a := Finset.mem_singleton.mp (h w (fun _ _ => rfl))
    refine ⟨?_, hwa⟩
    
    by_contra hK
    
    obtain ⟨i, hi⟩ : ∃ i, i ∉ K := by
      by_contra hall
      exact hK (Finset.eq_univ_iff_forall.mpr (fun x => not_not.mp (fun hx => hall ⟨x, hx⟩)))
    
    set w' : ConfigSpace ι := Function.update w i (!w i) with hw'
    have hagree : ∀ e ∈ K, w' e = w e := by
      intro e he
      have hne : e ≠ i := by rintro rfl; exact hi he
      rw [hw', Function.update_of_ne hne]
    have : w' ∈ ({a} : Finset (ConfigSpace ι)) := h w' hagree
    rw [Finset.mem_singleton, ← hwa] at this
    
    have := congrFun this i
    rw [hw', Function.update_self] at this
    exact (Bool.not_ne_self (w i)) this
  · rintro ⟨rfl, rfl⟩
    
    intro w' hw'
    have : w' = w := funext (fun i => hw' i (Finset.mem_univ i))
    rw [this]; exact Finset.mem_singleton_self w



omit [Fintype ι] [DecidableEq ι] in

theorem rc80_compl_compl (w : ConfigSpace ι) : rc80_compl (rc80_compl w) = w := by
  funext i; simp only [rc80_compl, Bool.not_not]


theorem rc85_occ_empty_set_iff (B : Finset (ConfigSpace ι)) (w : ConfigSpace ι) :
    rc80_occ B (∅ : Finset ι) w = true ↔ B = Finset.univ := by
  unfold rc80_occ
  rw [decide_eq_true_eq]
  constructor
  · intro h
    
    refine Finset.eq_univ_iff_forall.mpr (fun x => ?_)
    exact h x (fun e he => absurd he (Finset.notMem_empty e))
  · rintro rfl
    intro w' _
    exact Finset.mem_univ w'





theorem rc85_disjOccG_singleton_left (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)) :
    rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B
      = if B = Finset.univ then {a} else ∅ := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hB : B = Finset.univ
  · rw [if_pos hB]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨K, L, _, hK, _⟩
      exact ((rc85_occ_singleton_iff a K w).mp hK).2
    · rintro rfl
      
      refine ⟨Finset.univ, ∅, Finset.disjoint_empty_right _, ?_, ?_⟩
      · rw [rc85_occ_singleton_iff]; exact ⟨rfl, rfl⟩
      · rw [rc85_occ_empty_set_iff]; exact hB
  · rw [if_neg hB]
    simp only [Finset.notMem_empty, iff_false, not_exists, not_and]
    intro K L hKL hK hL
    
    obtain ⟨hKu, hwa⟩ := (rc85_occ_singleton_iff a K w).mp hK
    subst hKu
    have hLempty : L = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact (Finset.disjoint_left.mp hKL (Finset.mem_univ x)) hx
    subst hLempty
    rw [rc85_occ_empty_set_iff] at hL
    exact absurd hL hB




theorem rc85_wall_singleton_left (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)) :
    (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card := by
  rw [rc85_disjOccG_singleton_left]
  by_cases hB : B = Finset.univ
  · rw [if_pos hB]
    
    have hR : rc80_reflInterG ({a} : Finset (ConfigSpace ι)) B = {a} := by
      ext x
      simp only [rc80_reflInterG, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, _⟩; rfl
      · rintro rfl
        exact ⟨rfl, by rw [hB]; exact Finset.mem_univ _⟩
    rw [hR]
  · rw [if_neg hB]; exact Nat.zero_le _



theorem rc85_disjOccG_singleton_right (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι) :
    rc80_disjOccG A ({b} : Finset (ConfigSpace ι))
      = if A = Finset.univ then {b} else ∅ := by
  ext w
  simp only [rc80_disjOccG, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hA : A = Finset.univ
  · rw [if_pos hA]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨K, L, _, _, hL⟩
      exact ((rc85_occ_singleton_iff b L w).mp hL).2
    · rintro rfl
      refine ⟨∅, Finset.univ, Finset.disjoint_empty_left _, ?_, ?_⟩
      · rw [rc85_occ_empty_set_iff]; exact hA
      · rw [rc85_occ_singleton_iff]; exact ⟨rfl, rfl⟩
  · rw [if_neg hA]
    simp only [Finset.notMem_empty, iff_false, not_exists, not_and]
    intro K L hKL hK hL
    obtain ⟨hLu, hwb⟩ := (rc85_occ_singleton_iff b L w).mp hL
    subst hLu
    have hKempty : K = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      exact (Finset.disjoint_right.mp hKL (Finset.mem_univ x)) hx
    subst hKempty
    rw [rc85_occ_empty_set_iff] at hK
    exact absurd hK hA




theorem rc85_wall_singleton_right (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι) :
    (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card := by
  rw [rc85_disjOccG_singleton_right]
  by_cases hA : A = Finset.univ
  · rw [if_pos hA]
    
    have hR : rc80_reflInterG A ({b} : Finset (ConfigSpace ι)) = {rc80_compl b} := by
      ext x
      simp only [rc80_reflInterG, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hxc⟩
        
        have : rc80_compl (rc80_compl x) = rc80_compl b := by rw [hxc]
        rw [rc80_compl_compl] at this
        exact this
      · rintro rfl
        refine ⟨by rw [hA]; exact Finset.mem_univ _, ?_⟩
        rw [rc80_compl_compl]
    rw [hR, Finset.card_singleton, Finset.card_singleton]
  · rw [if_neg hA]; exact Nat.zero_le _





theorem rc85_singletonWitness_left_fin3 :
    (rc80_disjOccG ({(fun _ => true)} : Finset (ConfigSpace (Fin 3))) Finset.univ).card
      ≤ (rc80_reflInterG ({(fun _ => true)} : Finset (ConfigSpace (Fin 3))) Finset.univ).card :=
  rc85_wall_singleton_left _ _



theorem rc85_singletonWitness_disjOcc_fin3 :
    rc80_disjOccG ({(fun _ => true)} : Finset (ConfigSpace (Fin 3))) Finset.univ
      = {(fun _ => true)} := by
  rw [rc85_disjOccG_singleton_left, if_pos rfl]


theorem rc85_emptyWitness_fin3 :
    rc80_disjOccG (∅ : Finset (ConfigSpace (Fin 3))) Finset.univ = ∅ :=
  rc85_disjOccG_empty_left _



open Classical in














theorem rc85_consolidation :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)),
        rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧
    
    (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)),
        (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card →
        (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card →
        (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
          ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧
    
    (∀ A B : Finset (ConfigSpace (Fin 2)),
        (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι),
        (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun _ _ hA hB => rc80_disjOcc_eq_inter_of_upper_lower hA hB,
   fun _ _ hA hB => rc82_disjOccG_eq_inter_of_lower_upper hA hB,
   fun A₁ B₁ A₂ B₂ => rc80_wall_product A₁ B₁ A₂ B₂,
   rc79_top_wall_fin2,
   fun B => rc85_wall_empty_left B,
   fun A => rc85_wall_empty_right A,
   fun a B => rc85_wall_singleton_left a B,
   fun A b => rc85_wall_singleton_right A b,
   rc82_reimerWprobCore_of_boxUnionBound⟩




theorem rc85_proved_subclasses :
    
    (∀ (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧
    (∀ (A : Finset (ConfigSpace ι)),
        (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧
    
    (∀ (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧
    (∀ (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι),
        (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) :=
  ⟨rc85_wall_empty_left, rc85_wall_empty_right, rc85_wall_singleton_left, rc85_wall_singleton_right⟩

open Classical in






















theorem rc85_status :
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)),
        rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B = ∅) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)),
        rc80_disjOccG A (∅ : Finset (ConfigSpace ι)) = ∅) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (K : Finset ι) (w : ConfigSpace ι),
        rc80_occ ({a} : Finset (ConfigSpace ι)) K w = true ↔ K = Finset.univ ∧ w = a) ∧
    
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)),
        (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι),
        (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) ∧
    
    (rc60_BoxUnionBound → ReimerWprobCore) :=
  ⟨fun B => rc85_disjOccG_empty_left B,
   fun A => rc85_disjOccG_empty_right A,
   fun a K w => rc85_occ_singleton_iff a K w,
   fun a B => rc85_wall_singleton_left a B,
   fun A b => rc85_wall_singleton_right A b,
   rc82_reimerWprobCore_of_boxUnionBound⟩

end StatMech.Walls
