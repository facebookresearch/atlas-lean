/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Code.Inequalities.PerOrbitCardClose

open Finset MeasureTheory
open scoped NNReal FinsetFamily

namespace StatMech.Walls

open StatMech ConfigSpace




















theorem rmr_swapInjection_one (A B : Set (ConfigSpace (Fin 1))) :
    r2k_SwapInjection A B := by
  classical
  by_cases hAall : ∀ ω' : ConfigSpace (Fin 1), ω' ∈ A
  · 
    refine ⟨fun _ => fun _ => true, ?_, (r2k_swapPair_const_injective _).injOn⟩
    intro p hp
    rw [mem_disjointOccurrence_fin1] at hp
    refine ⟨hAall _, ?_⟩
    have hp1B : p.1 ∈ B := by
      rcases hp with ⟨_, hB⟩ | ⟨_, hBall⟩
      · exact hB
      · exact hBall p.1
    have hsnd : swapGlue (fun _ => true) p.2 p.1 = p.1 := by funext i; simp [swapGlue]
    simpa only [swapPair_snd, hsnd] using hp1B
  · 
    refine ⟨fun _ => fun _ => false, ?_, (r2k_swapPair_const_injective _).injOn⟩
    intro p hp
    rw [mem_disjointOccurrence_fin1] at hp
    rcases hp with ⟨hAall', _⟩ | ⟨hp1A, hBall⟩
    · exact absurd hAall' hAall
    · refine ⟨?_, hBall _⟩
      have hfst : swapGlue (fun _ => false) p.1 p.2 = p.1 := by funext i; simp [swapGlue]
      simpa only [swapPair_fst, hfst] using hp1A



theorem rmr_perOrbitCard_one (A B : Set (ConfigSpace (Fin 1))) :
    PerOrbitCard A B :=
  perOrbitCard_of_swapInjection A B (rmr_swapInjection_one A B)



theorem rmr_slabCard_one (A B : Set (ConfigSpace (Fin 1))) :
    poc_SlabCard A B :=
  (poc_perOrbitCard_iff_slabCard A B).mp (rmr_perOrbitCard_one A B)



theorem rmr_reimerCardForm_one (A B : Set (ConfigSpace (Fin 1))) :
    poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (rmr_slabCard_one A B)





theorem rmr_reimer_wprob_one (φ : Fin 1 → Bool → ℝ)
    (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1)
    (A B : Set (ConfigSpace (Fin 1))) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  reimer_wprob_one φ hφ0 hφ1 A B















variable {α : Type*} [Fintype α] [DecidableEq α]






theorem rmr_card_eq_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : StatMech.DependsOn A (↑S)) (hB : StatMech.DependsOn B (↑T)) (hST : Disjoint S T)
    (k : ConfigSpace α × ConfigSpace α) :
    #(boxOrbit A B k) = #(imgOrbit A B k) := by
  classical
  have hbox : disjointOccurrence A B = A ∩ B :=
    disjointOccurrence_eq_inter_of_dependsOn hA hB (Finset.disjoint_coe.mpr hST)
  
  have hinv : ∀ p : ConfigSpace α × ConfigSpace α,
      swapPair (fun _ => fun a => decide (a ∉ S))
        (swapPair (fun _ => fun a => decide (a ∉ S)) p) = p := by
    intro p; ext a
    · simp only [swapPair_fst, swapPair_snd, swapGlue_apply]; by_cases h : a ∉ S <;> simp [h]
    · simp only [swapPair_fst, swapPair_snd, swapGlue_apply]; by_cases h : a ∉ S <;> simp [h]
  apply Finset.card_bij' (fun p _ => swapPair (fun _ => fun a => decide (a ∉ S)) p)
    (fun q _ => swapPair (fun _ => fun a => decide (a ∉ S)) q)
  · 
    intro p hp
    simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hpbox, hpk⟩ := hp
    rw [hbox] at hpbox
    simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, by rw [orbitKey_swapPair]; exact hpk⟩
    · 
      have hag : agreeOn (↑S : Set α) p.1 (swapPair (fun _ => fun a => decide (a ∉ S)) p).1 := by
        intro a ha; simp only [Finset.mem_coe] at ha
        simp only [swapPair_fst, swapGlue_apply,
          show ¬ a ∉ S from not_not.mpr ha, decide_false, Bool.false_eq_true, if_false]
      exact (hA p.1 _ hag).mp hpbox.1
    · 
      have hag : agreeOn (↑T : Set α) p.1 (swapPair (fun _ => fun a => decide (a ∉ S)) p).2 := by
        intro a ha; simp only [Finset.mem_coe] at ha
        have haS : a ∉ S := fun h => (Finset.disjoint_left.mp hST) h ha
        simp only [swapPair_snd, swapGlue_apply, decide_eq_true haS, if_true]
      exact (hB p.1 _ hag).mp hpbox.2
  · 
    intro q hq
    simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨hqA, hqB, hqk⟩ := hq
    simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, by rw [orbitKey_swapPair]; exact hqk⟩
    rw [hbox]
    refine ⟨?_, ?_⟩
    · 
      have hag : agreeOn (↑S : Set α) q.1 (swapPair (fun _ => fun a => decide (a ∉ S)) q).1 := by
        intro a ha; simp only [Finset.mem_coe] at ha
        simp only [swapPair_fst, swapGlue_apply,
          show ¬ a ∉ S from not_not.mpr ha, decide_false, Bool.false_eq_true, if_false]
      exact (hA q.1 _ hag).mp hqA
    · 
      have hag : agreeOn (↑T : Set α) q.2 (swapPair (fun _ => fun a => decide (a ∉ S)) q).1 := by
        intro a ha; simp only [Finset.mem_coe] at ha
        have haS : a ∉ S := fun h => (Finset.disjoint_left.mp hST) h ha
        simp only [swapPair_fst, swapGlue_apply, decide_eq_true haS, if_true]
      exact (hB q.2 _ hag).mp hqB
  · intro p _; exact hinv p
  · intro q _; exact hinv q




theorem rmr_slabCard_eq_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : StatMech.DependsOn A (↑S)) (hB : StatMech.DependsOn B (↑T)) (hST : Disjoint S T)
    (k : ConfigSpace α × ConfigSpace α) :
    #(poc_slabBox A B k) = #(poc_slabImg A B k) := by
  rw [← poc_card_boxOrbit, ← poc_card_imgOrbit]
  exact rmr_card_eq_of_disjoint_support hA hB hST k



theorem rmr_slabCard_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : StatMech.DependsOn A (↑S)) (hB : StatMech.DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_SlabCard A B :=
  fun k => le_of_eq (rmr_slabCard_eq_of_disjoint_support hA hB hST k)


theorem rmr_reimerCardForm_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : StatMech.DependsOn A (↑S)) (hB : StatMech.DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (rmr_slabCard_of_disjoint_support hA hB hST)





theorem rmr_reimer_wprob_eq_of_disjoint_support (φ : α → Bool → ℝ)
    (hφ1 : ∀ x, φ x false + φ x true = 1)
    {A B : Set (ConfigSpace α)} {S T : Set α}
    (hA : StatMech.DependsOn A S) (hB : StatMech.DependsOn B T) (hST : Disjoint S T) :
    wprob φ (disjointOccurrence A B) = wprob φ A * wprob φ B :=
  reimer_wprob_of_disjoint_support φ hφ1 hA hB hST

end StatMech.Walls
