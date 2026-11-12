/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Code.Walls.rc33nonlocal
import Code.Walls.rc56sandwich
import Code.Inequalities.ReimerDoubled
import Mathlib.Combinatorics.Hall.Basic

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}
















noncomputable def rc59_dblPair (S R : Finset (Fin n)) : Finset (Fin n ⊕ Fin n) :=
  StatMech.dbl S R


lemma rc59_dblPair_inl (S R : Finset (Fin n)) (a : Fin n) :
    (Sum.inl a) ∈ rc59_dblPair S R ↔ a ∈ S := by
  simp [rc59_dblPair, StatMech.mem_dbl_inl]


lemma rc59_dblPair_inr (S R : Finset (Fin n)) (a : Fin n) :
    (Sum.inr a) ∈ rc59_dblPair S R ↔ a ∈ R := by
  simp [rc59_dblPair, StatMech.mem_dbl_inr]




lemma rc59_dblPair_injective :
    Function.Injective (fun p : Finset (Fin n) × Finset (Fin n) => rc59_dblPair p.1 p.2) :=
  StatMech.dbl_injective





noncomputable def rc59_doubledCover (𝒯 : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Finset (Fin n)) : Finset (Finset (Fin n ⊕ Fin n)) :=
  𝒯.image (fun S => rc59_dblPair S (f S))




lemma rc59_doubledCover_card (𝒯 : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Finset (Fin n)) :
    (rc59_doubledCover 𝒯 f).card = 𝒯.card := by
  unfold rc59_doubledCover
  refine Finset.card_image_of_injOn ?_
  intro S hS S' hS' h
  have : rc59_dblPair S (f S) = rc59_dblPair S' (f S') := h
  
  ext a
  rw [← rc59_dblPair_inl S (f S) a, ← rc59_dblPair_inl S' (f S') a, this]











noncomputable def rc59_reimerReflection (S K L : Finset (Fin n)) : Finset (Fin n ⊕ Fin n) :=
  rc59_dblPair S (rc36_R0 S K L)


lemma rc59_reimerReflection_inl (S K L : Finset (Fin n)) (a : Fin n) :
    (Sum.inl a) ∈ rc59_reimerReflection S K L ↔ a ∈ S := by
  simp [rc59_reimerReflection, rc59_dblPair_inl]


lemma rc59_reimerReflection_inr (S K L : Finset (Fin n)) (a : Fin n) :
    (Sum.inr a) ∈ rc59_reimerReflection S K L ↔ a ∈ rc36_R0 S K L := by
  simp [rc59_reimerReflection, rc59_dblPair_inr]





theorem rc59_reimerReflection_mem_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K L : Finset (Fin n)} (hKL : Disjoint K L)
    (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) :
    rc36_R0 S K L ∈ rc10_reflInter 𝒜 ℬ :=
  rc36_R0_mem_reflInter 𝒜 ℬ hKL hKA hLB




















def rc59_leftFactor (𝒜 : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  rc37_admLeft n 𝒜 S


def rc59_rightFactor (ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  rc37_rightMem n ℬ




def rc59_nbhd (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  rc59_leftFactor 𝒜 S ∩ rc59_rightFactor ℬ




theorem rc59_nbhd_eq_admOneSidedA (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc59_nbhd 𝒜 ℬ S = rc33_admOneSidedA n 𝒜 ℬ S := by
  rw [rc59_nbhd, rc59_leftFactor, rc59_rightFactor, ← rc37_admOneSidedA_eq_inter]




theorem rc59_rightFactor_indep (ℬ : Finset (Finset (Fin n))) (S S' : Finset (Fin n)) :
    rc59_rightFactor ℬ = rc59_rightFactor ℬ ∧
      (rc59_nbhd 𝒜 ℬ S = rc59_leftFactor 𝒜 S ∩ rc59_rightFactor ℬ ∧
       rc59_nbhd 𝒜 ℬ S' = rc59_leftFactor 𝒜 S' ∩ rc59_rightFactor ℬ) := by
  exact ⟨rfl, rfl, rfl⟩




theorem rc59_reflInter_eq_inter_rightFactor (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc59_rightFactor ℬ := by
  ext R
  rw [rc20_mem_reflInter, rc59_rightFactor, rc37_rightMem, Finset.mem_inter, Finset.mem_filter,
    decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, Finset.mem_univ _, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

open Classical in











def rc59_IndepHall : Prop :=
  ∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))),
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card

open Classical in




theorem rc59_wall_of_indepHall_pair (𝒜 ℬ : Finset (Finset (Fin n)))
    (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  refine rc33_wall_of_hallOneSidedA n 𝒜 ℬ ?_
  intro 𝒯 h𝒯
  have h := hHall 𝒯 h𝒯
  refine h.trans (le_of_eq ?_)
  congr 1
  apply Finset.biUnion_congr rfl
  intro S _
  exact rc59_nbhd_eq_admOneSidedA 𝒜 ℬ S






theorem rc59_famCylBoxResidue_of_indepHall (h : rc59_IndepHall) : rc20_FamCylBoxResidue := by
  intro m 𝒜 ℬ
  exact rc59_wall_of_indepHall_pair 𝒜 ℬ (h m 𝒜 ℬ)






theorem rc59_reimerWprobCore_of_indepHall (h : rc59_IndepHall) : ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter
    (rc20_cylBoxReflInter_of_famCylBoxResidue (rc59_famCylBoxResidue_of_indepHall h))













open Classical in


theorem rc59_biUnion_nbhd_eq (𝒜 ℬ : Finset (Finset (Fin n))) (𝒯 : Finset (Finset (Fin n))) :
    𝒯.biUnion (rc59_nbhd 𝒜 ℬ) = 𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ) :=
  Finset.biUnion_congr rfl (fun S _ => rc59_nbhd_eq_admOneSidedA 𝒜 ℬ S)

open Classical in

theorem rc59_indepHall_pair_iff (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card) ↔
    (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) := by
  constructor
  · intro h 𝒯 h𝒯; have := h 𝒯 h𝒯; rwa [rc59_biUnion_nbhd_eq] at this
  · intro h 𝒯 h𝒯; have := h 𝒯 h𝒯; rwa [rc59_biUnion_nbhd_eq]

open Classical in

theorem rc59_indepHall_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  (rc59_indepHall_pair_iff 𝒜 ℬ).mpr
    (rc33_hallOneSidedA_prop_of_bool 0 𝒜 ℬ (rc33_hallOneSidedA_fin0 𝒜 ℬ))

open Classical in

theorem rc59_indepHall_fin1 (𝒜 ℬ : Finset (Finset (Fin 1))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  (rc59_indepHall_pair_iff 𝒜 ℬ).mpr
    (rc33_hallOneSidedA_prop_of_bool 1 𝒜 ℬ (rc33_hallOneSidedA_fin1 𝒜 ℬ))

open Classical in



theorem rc59_indepHall_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd 𝒜 ℬ)).card :=
  (rc59_indepHall_pair_iff 𝒜 ℬ).mpr
    (rc33_hallOneSidedA_prop_of_bool 2 𝒜 ℬ (rc33_hallOneSidedA_fin2 𝒜 ℬ))

open Classical in



theorem rc59_wall_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc59_wall_of_indepHall_pair 𝒜 ℬ (rc59_indepHall_fin2 𝒜 ℬ)
















open Classical in




theorem rc59_indepHall_fin3_refuter :
    ∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card :=
  (rc59_indepHall_pair_iff rc32_A3 rc32_B3).mpr
    (rc33_hallOneSidedA_prop_of_bool 3 rc32_A3 rc32_B3 rc33_hallOneSidedA_fin3_refuter)

open Classical in





theorem rc59_wall_fin3_refuter :
    #(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3) :=
  rc59_wall_of_indepHall_pair rc32_A3 rc32_B3 rc59_indepHall_fin3_refuter







theorem rc59_nbhd_proper_fin3 :
    rc59_nbhd rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3 := by
  rw [rc59_nbhd_eq_admOneSidedA]; exact rc33_admOneSidedA_proper_fin3








theorem rc59_reimerReflection_not_injective_fin3 :
    ((rc21_boxComp 3 rc32_A3 rc32_B3).biUnion
        (fun S => (rc21_symmWitComp 3 rc32_A3 rc32_B3 S).image (fun L => symmDiff S L))).card
      < (rc21_boxComp 3 rc32_A3 rc32_B3).card :=
  rc32_symmDiffMirror_fin3_refuted






























theorem rc59_status :
    (rc59_IndepHall → ReimerWprobCore) ∧
    (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc59_nbhd rc32_A3 rc32_B3)).card) ∧
    (#(rc20_famCylBox rc32_A3 rc32_B3) ≤ #(rc10_reflInter rc32_A3 rc32_B3)) ∧
    (rc59_nbhd rc32_A3 rc32_B3 {1} ≠ rc10_reflInter rc32_A3 rc32_B3) :=
  ⟨rc59_reimerWprobCore_of_indepHall, rc59_indepHall_fin3_refuter, rc59_wall_fin3_refuter,
    rc59_nbhd_proper_fin3⟩

end StatMech.Walls
