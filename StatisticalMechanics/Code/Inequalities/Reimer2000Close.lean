/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Code.Inequalities.ReimerPairWitnessClose

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









def swapGlue (S : α → Bool) (ω τ : ConfigSpace α) : ConfigSpace α :=
  fun a => if S a then τ a else ω a

omit [Fintype α] [DecidableEq α] in
@[simp] lemma swapGlue_apply (S : α → Bool) (ω τ : ConfigSpace α) (a : α) :
    swapGlue S ω τ a = if S a then τ a else ω a := rfl

omit [DecidableEq α] in







lemma swapPair_weight (φ : α → Bool → ℝ) (S : α → Bool) (ω τ : ConfigSpace α) :
    pweight φ (swapGlue S ω τ) * pweight φ (swapGlue S τ ω) = pweight φ ω * pweight φ τ := by
  simp only [pweight, swapGlue]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun a _ => by by_cases h : S a <;> simp [h, mul_comm])

omit [Fintype α] [DecidableEq α] in



lemma swapGlue_swapGlue_left (S : α → Bool) (ω τ : ConfigSpace α) :
    swapGlue S (swapGlue S ω τ) (swapGlue S τ ω) = ω := by
  funext a; simp only [swapGlue]; by_cases h : S a <;> simp [h]

omit [Fintype α] [DecidableEq α] in

lemma swapGlue_swapGlue_right (S : α → Bool) (ω τ : ConfigSpace α) :
    swapGlue S (swapGlue S τ ω) (swapGlue S ω τ) = τ := by
  funext a; simp only [swapGlue]; by_cases h : S a <;> simp [h]








def swapPair (σ : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : ConfigSpace α × ConfigSpace α :=
  (swapGlue (σ p) p.1 p.2, swapGlue (σ p) p.2 p.1)

omit [Fintype α] [DecidableEq α] in
@[simp] lemma swapPair_fst (σ : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : (swapPair σ p).1 = swapGlue (σ p) p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] lemma swapPair_snd (σ : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : (swapPair σ p).2 = swapGlue (σ p) p.2 p.1 := rfl
















def r2k_SwapInjection (A B : Set (ConfigSpace α)) : Prop :=
  ∃ σ : ConfigSpace α × ConfigSpace α → (α → Bool),
    (∀ p : ConfigSpace α × ConfigSpace α, p.1 ∈ disjointOccurrence A B →
        (swapPair σ p).1 ∈ A ∧ (swapPair σ p).2 ∈ B) ∧
    Set.InjOn (swapPair σ) {p : ConfigSpace α × ConfigSpace α | p.1 ∈ disjointOccurrence A B}








omit [DecidableEq α] in




theorem r2k_weightInjection_of_swapInjection {A B : Set (ConfigSpace α)}
    (hSI : r2k_SwapInjection A B) : rpw_WeightInjection A B := by
  obtain ⟨σ, hmem, hinj⟩ := hSI
  refine ⟨swapPair σ, hmem, ?_, hinj⟩
  intro φ p _
  simp only [swapPair_fst, swapPair_snd]
  exact swapPair_weight φ (σ p) p.1 p.2





theorem r2k_reimer_wprob_of_swapInjection (φ : α → Bool → ℝ) (hφ0 : ∀ x b, 0 ≤ φ x b)
    (hφ1 : ∀ x, φ x false + φ x true = 1) {A B : Set (ConfigSpace α)}
    (hSI : r2k_SwapInjection A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  rpw_reimer_wprob_of_weightInjection φ hφ0 hφ1 (r2k_weightInjection_of_swapInjection hSI)








omit [Fintype α] [DecidableEq α] in


theorem r2k_swapPair_const_injective (S₀ : α → Bool) :
    Function.Injective (swapPair (fun _ => S₀) : ConfigSpace α × ConfigSpace α → _) := by
  intro p q h
  simp only [swapPair] at h
  have h1 : swapGlue S₀ p.1 p.2 = swapGlue S₀ q.1 q.2 := congrArg Prod.fst h
  have h2 : swapGlue S₀ p.2 p.1 = swapGlue S₀ q.2 q.1 := congrArg Prod.snd h
  ext a
  · rw [show p.1 = swapGlue S₀ (swapGlue S₀ p.1 p.2) (swapGlue S₀ p.2 p.1) from
      (swapGlue_swapGlue_left S₀ p.1 p.2).symm, h1, h2, swapGlue_swapGlue_left S₀ q.1 q.2]
  · rw [show p.2 = swapGlue S₀ (swapGlue S₀ p.2 p.1) (swapGlue S₀ p.1 p.2) from
      (swapGlue_swapGlue_right S₀ p.1 p.2).symm, h1, h2, swapGlue_swapGlue_right S₀ q.1 q.2]








omit [Fintype α] in





theorem r2k_swapInjection_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    r2k_SwapInjection A B := by
  classical
  
  refine ⟨fun _ => fun a => decide (a ∉ S), ?_,
    (r2k_swapPair_const_injective (fun a => decide (a ∉ S))).injOn⟩
  intro p hp
  
  have hagA : agreeOn (↑S : Set α) p.1 (swapGlue (fun a => decide (a ∉ S)) p.1 p.2) := by
    intro a ha
    simp only [Finset.mem_coe] at ha
    have : ¬ a ∉ S := not_not.mpr ha
    simp only [swapGlue_apply, this, decide_false, Bool.false_eq_true, if_false]
  
  have hagB : agreeOn (↑T : Set α) p.1 (swapGlue (fun a => decide (a ∉ S)) p.2 p.1) := by
    intro a ha
    simp only [Finset.mem_coe] at ha
    have haS : a ∉ S := fun h => (Finset.disjoint_left.mp hST) h ha
    have : decide (a ∉ S) = true := decide_eq_true haS
    simp only [swapGlue_apply, this, if_true]
  refine ⟨?_, ?_⟩
  · 
    have hp1A : p.1 ∈ A := (disjointOccurrence_subset_inter A B hp).1
    exact (hA p.1 _ hagA).mp hp1A
  · 
    have hp1B : p.1 ∈ B := (disjointOccurrence_subset_inter A B hp).2
    exact (hB p.1 _ hagB).mp hp1B



omit [Fintype α] [DecidableEq α] in


theorem r2k_swapInjection_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : r2k_SwapInjection A B := by
  refine ⟨fun _ => fun _ => false, ?_, ?_⟩
  · intro p hp; rw [hbox] at hp; exact absurd hp (Set.notMem_empty p.1)
  · intro p hp; rw [Set.mem_setOf_eq, hbox] at hp; exact absurd hp (Set.notMem_empty p.1)




def r2k_SwapInjectionAll : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), r2k_SwapInjection A B



theorem r2k_reimer_wprob_core_of_swapInjection (h : r2k_SwapInjectionAll) : ReimerWprobCore := by
  intro n φ hφ0 hφ1 A B
  exact r2k_reimer_wprob_of_swapInjection φ hφ0 hφ1 (h n A B)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in

theorem r2k_reimer_inequality_of_swapInjection (h : r2k_SwapInjectionAll) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (r2k_reimer_wprob_core_of_swapInjection h) hp A B



















def r2k_rbi_swap : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) → (Fin 2 → Bool) :=
  fun p => fun a =>
    if a = 0 then (p.2 0 && !p.2 1)
    else (p.2 0 && !p.2 1 && p.1 1)



lemma r2k_rbi_box_fst {ω : ConfigSpace (Fin 2)} (hω : ω ∈ disjointOccurrence rbi_A rbi_B) :
    ω 0 = false := by
  rw [rbi_box_eq] at hω
  rcases hω with h | h
  · rw [h]; rfl
  · rw [Set.mem_singleton_iff] at h; rw [h]; rfl






theorem r2k_swapInjection_rbi : r2k_SwapInjection rbi_A rbi_B := by
  classical
  refine ⟨r2k_rbi_swap, ?_, ?_⟩
  · 
    rintro ⟨ω, τ⟩ hp
    have hω0 : ω 0 = false := r2k_rbi_box_fst hp
    
    simp only [swapPair_fst, swapPair_snd, rbi_A, rbi_B, Set.mem_setOf_eq, swapGlue_apply,
      r2k_rbi_swap, hω0, Fin.isValue,
      show ((1 : Fin 2) = 0) = False from by decide, if_false]
    
    clear hp hω0
    cases ω 1 <;> cases τ 0 <;> cases τ 1 <;> decide
  · 
    rintro ⟨ω, τ⟩ hp ⟨ω', τ'⟩ hp' heq
    have hω0 : ω 0 = false := r2k_rbi_box_fst hp
    have hω0' : ω' 0 = false := r2k_rbi_box_fst hp'
    
    have e1 := congrArg (fun q => q.1) heq
    have e2 := congrArg (fun q => q.2) heq
    simp only [swapPair_fst, swapPair_snd] at e1 e2
    have e10 := congrFun e1 0; have e11 := congrFun e1 1
    have e20 := congrFun e2 0; have e21 := congrFun e2 1
    simp only [swapGlue_apply, r2k_rbi_swap, hω0, hω0', Fin.isValue,
      show ((1 : Fin 2) = 0) = False by decide, if_false] at e10 e11 e20 e21
    
    have hext : ω 1 = ω' 1 ∧ τ 0 = τ' 0 ∧ τ 1 = τ' 1 →
        (⟨ω, τ⟩ : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) = ⟨ω', τ'⟩ := by
      rintro ⟨h1, h2, h3⟩
      refine Prod.ext ?_ ?_ <;> funext i <;> fin_cases i <;>
        simp_all [Fin.isValue]
    apply hext
    
    clear hp hp' heq e1 e2 hω0 hω0' hext
    revert e10 e11 e20 e21
    cases ω 1 <;> cases ω' 1 <;> cases τ 0 <;> cases τ 1 <;>
      cases τ' 0 <;> cases τ' 1 <;> decide

end StatMech
