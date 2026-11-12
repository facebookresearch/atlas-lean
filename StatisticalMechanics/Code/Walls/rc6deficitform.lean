/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Code.Walls.rmr_reflectinvolution
import Code.Walls.rc3_core

open Finset
open scoped StatMech

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]








omit [Fintype α] [DecidableEq α] in



theorem rc6_compl_involutive :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α) :=
  rmr_compl_involutive





def rc6_complEquiv : ConfigSpace α ≃ ConfigSpace α :=
  Function.Involutive.toPerm rmr_compl rmr_compl_involutive

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc6_complEquiv_apply (ω : ConfigSpace α) : rc6_complEquiv ω = rmr_compl ω :=
  rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc6_complEquiv_symm_apply (ω : ConfigSpace α) :
    rc6_complEquiv.symm ω = rmr_compl ω := rfl

omit [Fintype α] [DecidableEq α] in


theorem rc6_complEquiv_symm : (rc6_complEquiv : ConfigSpace α ≃ ConfigSpace α).symm
    = rc6_complEquiv := rfl








open Classical in



theorem rc6_card_compl_mem (B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) :=
  rmr_card_compl_mem B

open Classical in


theorem rc6_card_reflect (B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ rmr_reflect B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) :=
  rmr_card_reflect B

open Classical in


theorem rc6_RHS_eq_inter (A B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) :=
  rmr_RHS_eq_inter A B











open Classical in



noncomputable def rc6_deficit (A B : Set (ConfigSpace α)) : ℤ :=
  (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ)
    - (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) : ℤ)

open Classical in



theorem rc6_deficit_eq (A B : Set (ConfigSpace α)) :
    rc6_deficit A B =
      (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ)
        - (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) : ℤ) :=
  rfl

open Classical in





theorem rc6_reimerCardForm_iff_deficit (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔ rc6_deficit A B ≤ 0 := by
  rw [rmr_reimerCardForm_iff_inter]
  unfold rc6_deficit
  omega










def rc6_DeficitNonpos : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rc6_deficit A B ≤ 0




theorem rc6_deficitNonpos_iff_reimerCardFormAll :
    rc6_DeficitNonpos ↔ ReimerCardFormAll := by
  unfold rc6_DeficitNonpos ReimerCardFormAll
  constructor
  · intro h n A B; exact (rc6_reimerCardForm_iff_deficit A B).mpr (h n A B)
  · intro h n A B; exact (rc6_reimerCardForm_iff_deficit A B).mp (h n A B)








open Classical in

theorem rc6_deficit_rbi : rc6_deficit rbi_A rbi_B ≤ 0 :=
  (rc6_reimerCardForm_iff_deficit rbi_A rbi_B).mp rc3_core_reimerCardForm_rbi

open Classical in


theorem rc6_deficit_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc6_deficit A B ≤ 0 :=
  (rc6_reimerCardForm_iff_deficit A B).mp
    (rc3_core_reimerCardForm_of_disjoint_support hA hB hST)

open Classical in


theorem rc6_deficit_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rc6_deficit A B ≤ 0 :=
  (rc6_reimerCardForm_iff_deficit A B).mp (rc3_core_reimerCardForm_of_box_empty hbox)

open Classical in


theorem rc6_deficit_one (A B : Set (ConfigSpace (Fin 1))) : rc6_deficit A B ≤ 0 :=
  (rc6_reimerCardForm_iff_deficit A B).mp (rc3_core_reimerCardForm_one A B)













open Classical in








theorem rc6_deficit_form (A B : Set (ConfigSpace α)) :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α)
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)))
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)))
      ∧ (StatMech.poc_ReimerCardForm A B ↔ rc6_deficit A B ≤ 0) :=
  ⟨rc6_compl_involutive, rc6_card_compl_mem B, rc6_RHS_eq_inter A B,
    rc6_reimerCardForm_iff_deficit A B⟩

end StatMech.Walls
