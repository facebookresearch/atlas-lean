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



theorem rc5_compl_involutive :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α) :=
  rmr_compl_involutive





def rc5_complEquiv : ConfigSpace α ≃ ConfigSpace α :=
  Function.Involutive.toPerm rmr_compl rmr_compl_involutive

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc5_complEquiv_apply (ω : ConfigSpace α) : rc5_complEquiv ω = rmr_compl ω :=
  rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem rc5_complEquiv_symm_apply (ω : ConfigSpace α) :
    rc5_complEquiv.symm ω = rmr_compl ω := rfl

omit [Fintype α] [DecidableEq α] in


theorem rc5_complEquiv_symm : (rc5_complEquiv : ConfigSpace α ≃ ConfigSpace α).symm
    = rc5_complEquiv := rfl








open Classical in



theorem rc5_card_compl_mem (B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) :=
  rmr_card_compl_mem B

open Classical in


theorem rc5_card_reflect (B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ rmr_reflect B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)) :=
  rmr_card_reflect B

open Classical in


theorem rc5_RHS_eq_inter (A B : Set (ConfigSpace α)) :
    #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
      = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) :=
  rmr_RHS_eq_inter A B











open Classical in




noncomputable def rc5_deficit (A B : Set (ConfigSpace α)) : ℤ :=
  (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ)
    - (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) : ℤ)

open Classical in




theorem rc5_reimerCardForm_iff_deficit (A B : Set (ConfigSpace α)) :
    StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0 := by
  rw [rmr_reimerCardForm_iff_inter]
  unfold rc5_deficit
  omega

open Classical in




theorem rc5_deficit_eq (A B : Set (ConfigSpace α)) :
    rc5_deficit A B =
      (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B)) : ℤ)
        - (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)) : ℤ) :=
  rfl












def rc5_DeficitNonpos : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rc5_deficit A B ≤ 0





theorem rc5_deficitNonpos_iff_reimerCardFormAll :
    rc5_DeficitNonpos ↔ ReimerCardFormAll := by
  unfold rc5_DeficitNonpos ReimerCardFormAll
  constructor
  · intro h n A B; exact (rc5_reimerCardForm_iff_deficit A B).mpr (h n A B)
  · intro h n A B; exact (rc5_reimerCardForm_iff_deficit A B).mp (h n A B)








open Classical in



theorem rc5_deficit_rbi : rc5_deficit rbi_A rbi_B ≤ 0 :=
  (rc5_reimerCardForm_iff_deficit rbi_A rbi_B).mp rc3_core_reimerCardForm_rbi

open Classical in


theorem rc5_deficit_of_disjoint_support {A B : Set (ConfigSpace α)} {S T : Finset α}
    (hA : DependsOn A (↑S)) (hB : DependsOn B (↑T)) (hST : Disjoint S T) :
    rc5_deficit A B ≤ 0 :=
  (rc5_reimerCardForm_iff_deficit A B).mp
    (rc3_core_reimerCardForm_of_disjoint_support hA hB hST)

open Classical in


theorem rc5_deficit_of_box_empty {A B : Set (ConfigSpace α)}
    (hbox : disjointOccurrence A B = ∅) : rc5_deficit A B ≤ 0 :=
  (rc5_reimerCardForm_iff_deficit A B).mp (rc3_core_reimerCardForm_of_box_empty hbox)

open Classical in


theorem rc5_deficit_one (A B : Set (ConfigSpace (Fin 1))) : rc5_deficit A B ≤ 0 :=
  (rc5_reimerCardForm_iff_deficit A B).mp (rc3_core_reimerCardForm_one A B)













open Classical in












theorem rc5_reflect_involution (A B : Set (ConfigSpace α)) :
    Function.Involutive (rmr_compl : ConfigSpace α → ConfigSpace α)
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => rmr_compl ω ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ B)))
      ∧ (#(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∧ (fun a => !ω a) ∈ B))
          = #(Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B)))
      ∧ (StatMech.poc_ReimerCardForm A B ↔ rc5_deficit A B ≤ 0) :=
  ⟨rc5_compl_involutive, rc5_card_compl_mem B, rc5_RHS_eq_inter A B,
    rc5_reimerCardForm_iff_deficit A B⟩

end StatMech.Walls
