/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.Walls.rc4_core
import Code.Walls.rc3_core
import Code.Inequalities.PerOrbitCardClose
import Code.Inequalities.ReimerButterflyInjClose

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]














theorem rc5_reimerCardForm_rbi : poc_ReimerCardForm rbi_A rbi_B :=
  poc_reimerCardForm_of_slabCard rbi_A rbi_B poc_slabCard_rbi





theorem rc5_reimerCardForm_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (poc_slabCard_of_disjoint_support hA hB hST)



theorem rc5_reimerCardForm_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (poc_slabCard_of_box_empty hbox)




theorem rc5_reimerCardForm_one (A B : Set (ConfigSpace (Fin 1))) : poc_ReimerCardForm A B :=
  poc_reimerCardForm_of_slabCard A B (rc_core_bridge_one A B)










open Classical in





theorem rc5_reimerCardForm_rbi_nonvacuous :
    2 ≤ #(univ.filter (fun ω : ConfigSpace (Fin 2) => ω ∈ disjointOccurrence rbi_A rbi_B)) := by
  have hsub : ({rbi_cfg false false, rbi_cfg false true} : Finset (ConfigSpace (Fin 2)))
      ⊆ univ.filter (fun ω => ω ∈ disjointOccurrence rbi_A rbi_B) := by
    intro ω hω
    simp only [Finset.mem_insert, Finset.mem_singleton] at hω
    rcases hω with h | h <;> subst h
    · simp only [mem_filter, mem_univ, true_and]; exact rbi_FF_in_box
    · simp only [mem_filter, mem_univ, true_and]; exact rbi_FT_in_box
  have hne : rbi_cfg false false ≠ rbi_cfg false true := by
    intro h
    have := congrArg (fun q => q 1) h
    simp only [rbi_cfg_one] at this
    exact absurd this (by decide)
  have hcard2 : #({rbi_cfg false false, rbi_cfg false true}
      : Finset (ConfigSpace (Fin 2))) = 2 := Finset.card_pair hne
  calc 2 = #({rbi_cfg false false, rbi_cfg false true} : Finset (ConfigSpace (Fin 2))) :=
        hcard2.symm
    _ ≤ #(univ.filter (fun ω => ω ∈ disjointOccurrence rbi_A rbi_B)) := Finset.card_le_card hsub






















theorem rc5_reimerCardForm_nonvacuity :
    poc_ReimerCardForm rbi_A rbi_B
      ∧ (∀ {A B : Set (ConfigSpace α)} {S T : Finset α},
          DependsOn A (↑S) → DependsOn B (↑T) → Disjoint S T → poc_ReimerCardForm A B)
      ∧ (∀ {A B : Set (ConfigSpace α)}, disjointOccurrence A B = ∅ → poc_ReimerCardForm A B)
      ∧ (∀ A B : Set (ConfigSpace (Fin 1)), poc_ReimerCardForm A B) :=
  ⟨rc5_reimerCardForm_rbi,
    fun hA hB hST => rc5_reimerCardForm_of_disjoint_support hA hB hST,
    fun hbox => rc5_reimerCardForm_of_box_empty hbox,
    rc5_reimerCardForm_one⟩













theorem rc5_slabCard_nonvacuity :
    poc_SlabCard rbi_A rbi_B
      ∧ (∀ {A B : Set (ConfigSpace α)} {S T : Finset α},
          DependsOn A (↑S) → DependsOn B (↑T) → Disjoint S T → poc_SlabCard A B)
      ∧ (∀ {A B : Set (ConfigSpace α)}, disjointOccurrence A B = ∅ → poc_SlabCard A B)
      ∧ (∀ A B : Set (ConfigSpace (Fin 1)), poc_SlabCard A B) :=
  ⟨poc_slabCard_rbi,
    fun hA hB hST => poc_slabCard_of_disjoint_support hA hB hST,
    fun hbox => poc_slabCard_of_box_empty hbox,
    rc_core_bridge_one⟩

end StatMech.Walls
