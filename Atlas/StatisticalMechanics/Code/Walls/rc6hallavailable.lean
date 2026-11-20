/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Code.Walls.rc6deficitform
import Code.Walls.rc2_hallavailable
import Mathlib.Combinatorics.Hall.Basic

open Finset Function
open scoped StatMech

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







open Classical in

noncomputable def rc6_boxFinset (A B : Set (ConfigSpace α)) : Finset (ConfigSpace α) :=
  Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)

open Classical in



noncomputable def rc6_imgFinset (A B : Set (ConfigSpace α)) : Finset (ConfigSpace α) :=
  Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B)

open Classical in
@[simp] theorem rc6_mem_boxFinset {A B : Set (ConfigSpace α)} {ω : ConfigSpace α} :
    ω ∈ rc6_boxFinset A B ↔ ω ∈ disjointOccurrence A B := by
  simp only [rc6_boxFinset, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
@[simp] theorem rc6_mem_imgFinset {A B : Set (ConfigSpace α)} {ω : ConfigSpace α} :
    ω ∈ rc6_imgFinset A B ↔ (ω ∈ A ∧ (fun a => !ω a) ∈ B) := by
  simp only [rc6_imgFinset, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in


theorem rc6_reimerCardForm_iff_card_le (A B : Set (ConfigSpace α)) :
    poc_ReimerCardForm A B ↔ #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B) :=
  Iff.rfl












theorem rc6_card_le_iff_embedding (A B : Set (ConfigSpace α)) :
    #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B) ↔
      Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
  rw [← Fintype.card_coe (rc6_boxFinset A B), ← Fintype.card_coe (rc6_imgFinset A B)]
  exact ⟨Function.Embedding.nonempty_of_card_le,
    fun ⟨e⟩ => Fintype.card_le_of_embedding e⟩








theorem rc6_reimerCardForm_iff_embedding (A B : Set (ConfigSpace α)) :
    poc_ReimerCardForm A B ↔
      Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
  rw [rc6_reimerCardForm_iff_card_le, rc6_card_le_iff_embedding]














def rc6_fullRel (A B : Set (ConfigSpace α)) :
    ↥(rc6_boxFinset A B) → ↥(rc6_imgFinset A B) → Prop := fun _ _ => True

instance rc6_fullRel_decidable (A B : Set (ConfigSpace α)) :
    DecidableRel (rc6_fullRel A B) := fun _ _ => instDecidableTrue

open Classical in


theorem rc6_fullRel_nbhd (A B : Set (ConfigSpace α))
    (Aset : Finset (↥(rc6_boxFinset A B))) (hne : Aset.Nonempty) :
    (Finset.univ.filter (fun b : ↥(rc6_imgFinset A B) => ∃ a ∈ Aset, rc6_fullRel A B a b))
      = Finset.univ := by
  obtain ⟨a, ha⟩ := hne
  apply Finset.filter_true_of_mem
  intro b _
  exact ⟨a, ha, trivial⟩

open Classical in




theorem rc6_hallCond_iff_card_le (A B : Set (ConfigSpace α)) :
    (∀ Aset : Finset (↥(rc6_boxFinset A B)),
        #Aset ≤ #{b | ∃ a ∈ Aset, rc6_fullRel A B a b})
      ↔ #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B) := by
  constructor
  · intro hHall
    by_cases hbox : (rc6_boxFinset A B).Nonempty
    · obtain ⟨ω0, hω0⟩ := hbox
      have hu : (Finset.univ : Finset (↥(rc6_boxFinset A B))).Nonempty :=
        ⟨⟨ω0, hω0⟩, Finset.mem_univ _⟩
      have h := hHall Finset.univ
      rw [rc6_fullRel_nbhd A B Finset.univ hu, Finset.card_univ, Finset.card_univ,
        Fintype.card_coe, Fintype.card_coe] at h
      exact h
    · rw [Finset.not_nonempty_iff_eq_empty] at hbox
      rw [hbox]; simp
  · intro hle Aset
    rcases Aset.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [rc6_fullRel_nbhd A B Aset hne, Finset.card_univ, Fintype.card_coe]
      calc #Aset ≤ Fintype.card (↥(rc6_boxFinset A B)) := Finset.card_le_univ _
        _ = #(rc6_boxFinset A B) := Fintype.card_coe _
        _ ≤ #(rc6_imgFinset A B) := hle

open Classical in





theorem rc6_hall_transversal (A B : Set (ConfigSpace α))
    (hle : #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B)) :
    ∃ f : ↥(rc6_boxFinset A B) → ↥(rc6_imgFinset A B),
      Injective f ∧ ∀ x, rc6_fullRel A B x (f x) := by
  classical
  exact rc2_hall_available (rc6_fullRel A B)
    ((rc6_hallCond_iff_card_le A B).mpr hle)

open Classical in




theorem rc6_hall_injection (A B : Set (ConfigSpace α))
    (hle : #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B)) :
    Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
  obtain ⟨f, hinj, _⟩ := rc6_hall_transversal A B hle
  exact ⟨⟨f, hinj⟩⟩







open Classical in






theorem rc6_box_to_img_injection (A B : Set (ConfigSpace α))
    (hle : #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B)) :
    ∃ f : ConfigSpace α → ConfigSpace α,
      Set.InjOn f (disjointOccurrence A B) ∧
      Set.MapsTo f (disjointOccurrence A B) {ω | ω ∈ A ∧ (fun a => !ω a) ∈ B} := by
  obtain ⟨e⟩ := (rc6_card_le_iff_embedding A B).mp hle
  refine ⟨fun ω => if hmem : ω ∈ rc6_boxFinset A B then (e ⟨ω, hmem⟩ : ConfigSpace α) else ω,
    ?_, ?_⟩
  · intro x hx y hy hxy
    rw [← rc6_mem_boxFinset] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext hxy))
  · intro x hx
    rw [← rc6_mem_boxFinset] at hx
    simp only [dif_pos hx, Set.mem_setOf_eq]
    have hprop := (e ⟨x, hx⟩).property
    rwa [rc6_mem_imgFinset] at hprop











theorem rc6_reimerCardFormAll_iff_embeddingAll :
    ReimerCardFormAll ↔
      ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))),
        Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
  unfold ReimerCardFormAll
  constructor
  · intro h n A B; exact (rc6_reimerCardForm_iff_embedding A B).mp (h n A B)
  · intro h n A B; exact (rc6_reimerCardForm_iff_embedding A B).mpr (h n A B)








open Classical in



theorem rc6_embedding_rbi :
    Nonempty (↥(rc6_boxFinset rbi_A rbi_B) ↪ ↥(rc6_imgFinset rbi_A rbi_B)) :=
  (rc6_reimerCardForm_iff_embedding rbi_A rbi_B).mp
    ((rc6_reimerCardForm_iff_deficit rbi_A rbi_B).mpr rc6_deficit_rbi)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open Classical in

theorem rc6_embedding_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) :=
  (rc6_reimerCardForm_iff_embedding A B).mp
    ((rc6_reimerCardForm_iff_deficit A B).mpr (rc6_deficit_of_disjoint_support hA hB hST))

open Classical in


theorem rc6_embedding_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) :
    Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) :=
  (rc6_reimerCardForm_iff_embedding A B).mp
    ((rc6_reimerCardForm_iff_deficit A B).mpr (rc6_deficit_of_box_empty hbox))

open Classical in

theorem rc6_embedding_one (A B : Set (ConfigSpace (Fin 1))) :
    Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) :=
  (rc6_reimerCardForm_iff_embedding A B).mp
    ((rc6_reimerCardForm_iff_deficit A B).mpr (rc6_deficit_one A B))









open Classical in








theorem rc6_hall_available (A B : Set (ConfigSpace α)) :
    (poc_ReimerCardForm A B ↔
        Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)))
      ∧ ((∀ Aset : Finset (↥(rc6_boxFinset A B)),
            #Aset ≤ #{b | ∃ a ∈ Aset, rc6_fullRel A B a b})
          ↔ #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B)) :=
  ⟨rc6_reimerCardForm_iff_embedding A B, rc6_hallCond_iff_card_le A B⟩

end StatMech.Walls
