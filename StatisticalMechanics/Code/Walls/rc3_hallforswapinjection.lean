/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Code.Inequalities.ReimerSwapInjClose
import Code.Walls.rc2_hallavailable
import Mathlib.Combinatorics.Hall.Basic

open Finset Function
open StatMech ConfigSpace

namespace StatMech.Walls

variable {α : Type*} [Fintype α] [DecidableEq α]












def swapRel (A B : Set (ConfigSpace α)) :
    {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} →
      (ConfigSpace α × ConfigSpace α) → Prop :=
  fun p q => sameOrbit p.val q ∧ q.1 ∈ A ∧ q.2 ∈ B














open Classical in










theorem rc3_hall_for_swapInjection (A B : Set (ConfigSpace α))
    (hHall : ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α //
          p.1 ∈ disjointOccurrence A B},
        #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q}) :
    ∃ f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} →
            (ConfigSpace α × ConfigSpace α),
        Injective f ∧ ∀ x, swapRel A B x (f x) := by
  classical
  exact rc2_hall_available (swapRel A B) hHall

open Classical in





theorem rc3_hall_for_swapInjection_iff (A B : Set (ConfigSpace α)) :
    (∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α //
          p.1 ∈ disjointOccurrence A B},
        #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q}) ↔
      ∃ f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} →
              (ConfigSpace α × ConfigSpace α),
          Injective f ∧ ∀ x, swapRel A B x (f x) :=
  rc2_hall_iff (swapRel A B)

open Classical in





theorem rc3_hallCond_of_transversal (A B : Set (ConfigSpace α))
    (h : ∃ f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} →
            (ConfigSpace α × ConfigSpace α),
        Injective f ∧ ∀ x, swapRel A B x (f x)) :
    ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α //
          p.1 ∈ disjointOccurrence A B},
        #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} :=
  rc2_hall_necessary (swapRel A B) h











open Classical in





theorem rc3_hallCond_of_perOrbitCard (A B : Set (ConfigSpace α)) (hpo : PerOrbitCard A B) :
    ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α //
          p.1 ∈ disjointOccurrence A B},
        #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} := by
  classical
  intro Aset
  set K := Aset.image (fun p => orbitKey p.val) with hK
  have hfib : #Aset = ∑ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k)) := by
    apply Finset.card_eq_sum_card_fiberwise
    intro p hp; exact Finset.mem_image_of_mem _ hp
  rw [hfib]
  have hkstep : ∀ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k)) ≤ #(imgOrbit A B k) := by
    intro k _
    refine le_trans ?_ (hpo k)
    apply Finset.card_le_card_of_injOn (fun p => p.val)
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      simp only [boxOrbit, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p.property, hp.2⟩
    · intro a _ b _ hab; exact Subtype.ext hab
  calc ∑ k ∈ K, #(Aset.filter (fun p => orbitKey p.val = k))
      ≤ ∑ k ∈ K, #(imgOrbit A B k) := Finset.sum_le_sum hkstep
    _ = #(K.biUnion (fun k => imgOrbit A B k)) := by
        rw [Finset.card_biUnion]
        intro k1 _ k2 _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        simp only [imgOrbit, Finset.mem_filter] at hq1 hq2
        exact hne (hq1.2.2.2 ▸ hq2.2.2.2)
    _ ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} := by
        apply Finset.card_le_card
        intro q hq
        rw [Finset.mem_biUnion] at hq
        obtain ⟨k, hkK, hqimg⟩ := hq
        simp only [imgOrbit, Finset.mem_filter] at hqimg
        rw [hK, Finset.mem_image] at hkK
        obtain ⟨p, hpA, hpk⟩ := hkK
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ q, p, hpA, ?_, hqimg.2.1, hqimg.2.2.1⟩
        rw [sameOrbit_iff_orbitKey, hpk, ← hqimg.2.2.2]








set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open Classical in





theorem rc3_swapInjection_of_transversal (A B : Set (ConfigSpace α))
    (f : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B} →
            (ConfigSpace α × ConfigSpace α))
    (hfinj : Injective f) (hfr : ∀ x, swapRel A B x (f x)) :
    r2k_SwapInjection A B := by
  classical
  set σ : ConfigSpace α × ConfigSpace α → (α → Bool) :=
    fun p => if hp : p.1 ∈ disjointOccurrence A B then
      (fun a => decide ((f ⟨p, hp⟩).1 a ≠ p.1 a)) else (fun _ => false) with hσ
  have hσbox : ∀ p (hp : p.1 ∈ disjointOccurrence A B), swapPair σ p = f ⟨p, hp⟩ := by
    intro p hp
    have hso : sameOrbit p (f ⟨p, hp⟩) := (hfr ⟨p, hp⟩).1
    have heq : swapPair (fun _ => fun a => decide ((f ⟨p, hp⟩).1 a ≠ p.1 a)) p = f ⟨p, hp⟩ :=
      (swapPair_eq_of_sameOrbit p (f ⟨p, hp⟩) hso).symm
    rw [← heq]
    simp only [swapPair, hσ, dif_pos hp]
  refine ⟨σ, ?_, ?_⟩
  · intro p hp
    have hmem := (hfr ⟨p, hp⟩).2
    rw [hσbox p hp]
    exact ⟨hmem.1, hmem.2⟩
  · intro p hp q hq heq
    rw [Set.mem_setOf_eq] at hp hq
    rw [hσbox p hp, hσbox q hq] at heq
    have hpq : (⟨p, hp⟩ : {p : ConfigSpace α × ConfigSpace α // p.1 ∈ disjointOccurrence A B})
        = ⟨q, hq⟩ := hfinj heq
    exact Subtype.ext_iff.mp hpq








open Classical in





theorem rc3_swapInjection_of_perOrbitCard' (A B : Set (ConfigSpace α)) (hpo : PerOrbitCard A B) :
    r2k_SwapInjection A B := by
  obtain ⟨f, hfinj, hfr⟩ := rc3_hall_for_swapInjection A B (rc3_hallCond_of_perOrbitCard A B hpo)
  exact rc3_swapInjection_of_transversal A B f hfinj hfr

open Classical in






theorem rc3_perOrbitCard_iff_hallCond (A B : Set (ConfigSpace α)) :
    PerOrbitCard A B ↔
      ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α //
            p.1 ∈ disjointOccurrence A B},
          #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} :=
  ⟨rc3_hallCond_of_perOrbitCard A B,
    fun hHall => by
      obtain ⟨f, hfinj, hfr⟩ := rc3_hall_for_swapInjection A B hHall
      exact perOrbitCard_of_swapInjection A B
        (rc3_swapInjection_of_transversal A B f hfinj hfr)⟩








open Classical in




theorem rc3_hallCond_rbi :
    ∀ Aset : Finset {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) //
          p.1 ∈ disjointOccurrence rbi_A rbi_B},
        #Aset ≤ #{q | ∃ a ∈ Aset, swapRel rbi_A rbi_B a q} :=
  rc3_hallCond_of_perOrbitCard rbi_A rbi_B perOrbitCard_rbi




theorem rc3_hall_for_swapInjection_rbi :
    ∃ f : {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) //
            p.1 ∈ disjointOccurrence rbi_A rbi_B} →
            (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)),
        Injective f ∧ ∀ x, swapRel rbi_A rbi_B x (f x) :=
  rc3_hall_for_swapInjection rbi_A rbi_B rc3_hallCond_rbi

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open Classical in


theorem rc3_hallCond_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α //
          p.1 ∈ disjointOccurrence A B},
        #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} :=
  rc3_hallCond_of_perOrbitCard A B (perOrbitCard_of_disjoint_support hA hB hST)

open Classical in



theorem rc3_hallCond_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) :
    ∀ Aset : Finset {p : ConfigSpace α × ConfigSpace α //
          p.1 ∈ disjointOccurrence A B},
        #Aset ≤ #{q | ∃ a ∈ Aset, swapRel A B a q} :=
  rc3_hallCond_of_perOrbitCard A B (perOrbitCard_of_box_empty hbox)

end StatMech.Walls
