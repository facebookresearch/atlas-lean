/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Code.Walls.rc67marriagesplit

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}







open Classical in



theorem rc68_Tin_subset_biUnion (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
    rc67_Tin 𝒜 ℬ T ⊆ T.biUnion (rc59_nbhd 𝒜 ℬ) :=
  rc67_Tin_subset_biUnion 𝒜 ℬ hbox

open Classical in



theorem rc68_biUnion_card_split (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
    (T.biUnion (rc59_nbhd 𝒜 ℬ)).card
      = ((T.biUnion (rc59_nbhd 𝒜 ℬ)) \ rc67_Tin 𝒜 ℬ T).card + (rc67_Tin 𝒜 ℬ T).card :=
  (Finset.card_sdiff_add_card_eq_card (rc68_Tin_subset_biUnion 𝒜 ℬ hbox)).symm












open Classical in



def rc68_CountForm (𝒜 ℬ : Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) : Prop :=
  (rc67_Toff 𝒜 ℬ T).card ≤ ((T.biUnion (rc59_nbhd 𝒜 ℬ)) \ rc67_Tin 𝒜 ℬ T).card

open Classical in











theorem rc68_marriage_of_countForm (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
    (hcount : rc68_CountForm 𝒜 ℬ T) :
    T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  rw [rc67_split_card 𝒜 ℬ T, rc68_biUnion_card_split 𝒜 ℬ hbox]
  rw [rc68_CountForm] at hcount
  omega

open Classical in









theorem rc68_countForm_of_marriage (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ)
    (hmar : T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) :
    rc68_CountForm 𝒜 ℬ T := by
  rw [rc68_CountForm]
  rw [rc67_split_card 𝒜 ℬ T, rc68_biUnion_card_split 𝒜 ℬ hbox] at hmar
  omega

open Classical in




theorem rc68_countForm_iff_marriage (𝒜 ℬ : Finset (Finset (Fin n)))
    {T : Finset (Finset (Fin n))} (hbox : ∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) :
    rc68_CountForm 𝒜 ℬ T ↔ T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  ⟨rc68_marriage_of_countForm 𝒜 ℬ hbox, rc68_countForm_of_marriage 𝒜 ℬ hbox⟩










open Classical in

theorem rc68_witness_Tin :
    rc67_Tin rc66_wA rc66_wB {∅, {0}} = ({∅} : Finset (Finset (Fin 2))) := by
  rw [rc67_Tin, rc10_reflInter]; decide

open Classical in

theorem rc68_witness_Toff :
    rc67_Toff rc66_wA rc66_wB {∅, {0}} = ({{0}} : Finset (Finset (Fin 2))) := by
  rw [rc67_Toff, rc10_reflInter]; decide

open Classical in


theorem rc68_witness_biUnion :
    ({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)
      = ({∅, {1}} : Finset (Finset (Fin 2))) := by
  rw [Finset.biUnion_insert, Finset.singleton_biUnion, rc59_nbhd_eq_admOneSidedA,
    rc59_nbhd_eq_admOneSidedA]
  decide

open Classical in





theorem rc68_witness_countForm_holds :
    rc68_CountForm rc66_wA rc66_wB ({∅, {0}} : Finset (Finset (Fin 2))) := by
  rw [rc68_CountForm, rc68_witness_Toff, rc68_witness_biUnion, rc68_witness_Tin]
  decide

open Classical in



theorem rc68_witness_marriage_via_count :
    ({∅, {0}} : Finset (Finset (Fin 2))).card
      ≤ (({∅, {0}} : Finset (Finset (Fin 2))).biUnion (rc59_nbhd rc66_wA rc66_wB)).card := by
  refine rc68_marriage_of_countForm rc66_wA rc66_wB ?_ rc68_witness_countForm_holds
  intro S hS
  rw [Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl
  · exact rc66_witness_box.2.1
  · exact rc66_witness_box.1








open Classical in



def rc68_CountFormLeaf : Prop :=
  ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
    ∀ T ∈ (rc20_famCylBox 𝒜 ℬ).powerset, rc68_CountForm 𝒜 ℬ T

open Classical in




theorem rc68_countFormLeaf_iff_indepHall : rc68_CountFormLeaf ↔ rc59_IndepHall := by
  constructor
  · intro h m 𝒜 ℬ T hT
    exact (rc68_countForm_iff_marriage 𝒜 ℬ (fun _S hS => Finset.mem_powerset.mp hT hS)).mp (h m 𝒜 ℬ T hT)
  · intro h m 𝒜 ℬ T hT
    exact (rc68_countForm_iff_marriage 𝒜 ℬ (fun _S hS => Finset.mem_powerset.mp hT hS)).mpr (h m 𝒜 ℬ T hT)

open Classical in




theorem rc68_reimerWprobCore_of_countFormLeaf (h : rc68_CountFormLeaf) : ReimerWprobCore :=
  rc59_reimerWprobCore_of_indepHall (rc68_countFormLeaf_iff_indepHall.mp h)



open Classical in




theorem rc68_countForm_fin2 (𝒜 ℬ : Finset (Finset (Fin 2)))
    (T : Finset (Finset (Fin 2))) (hT : T ∈ (rc20_famCylBox 𝒜 ℬ).powerset) :
    rc68_CountForm 𝒜 ℬ T :=
  rc68_countForm_of_marriage 𝒜 ℬ (fun _S hS => Finset.mem_powerset.mp hT hS)
    (rc59_indepHall_fin2 𝒜 ℬ T hT)



open Classical in






























theorem rc68_status :
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (T : Finset (Finset (Fin m))),
        (∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) → rc68_CountForm 𝒜 ℬ T →
        T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card) ∧
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) (T : Finset (Finset (Fin m))),
        (∀ S ∈ T, S ∈ rc20_famCylBox 𝒜 ℬ) →
        (rc68_CountForm 𝒜 ℬ T ↔ T.card ≤ (T.biUnion (rc59_nbhd 𝒜 ℬ)).card)) ∧
    (rc68_CountFormLeaf ↔ rc59_IndepHall) ∧
    
    (¬ ∃ g : Finset (Fin 2) → Finset (Fin 2),
        rc67_ForcedSelfMatchSDR rc66_wA rc66_wB {∅, {0}} g) ∧
    rc68_CountForm rc66_wA rc66_wB ({∅, {0}} : Finset (Finset (Fin 2))) ∧
    
    (rc68_CountFormLeaf → ReimerWprobCore) :=
  ⟨fun _m 𝒜 ℬ _T hbox hcount => rc68_marriage_of_countForm 𝒜 ℬ hbox hcount,
   fun _m 𝒜 ℬ _T hbox => rc68_countForm_iff_marriage 𝒜 ℬ hbox,
   rc68_countFormLeaf_iff_indepHall,
   rc67_forcedSelfMatch_fails_witness,
   rc68_witness_countForm_holds,
   rc68_reimerWprobCore_of_countFormLeaf⟩

end StatMech.Walls
