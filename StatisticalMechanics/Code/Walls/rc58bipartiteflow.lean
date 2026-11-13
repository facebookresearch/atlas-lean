/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.Walls.rc57witnessed
import Code.Walls.rc22doublecover
import Mathlib.Combinatorics.Hall.Basic

set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]











def rc58_Amono : Finset (Finset (Fin 2)) := {∅, {0}, {1}}


def rc58_Bmono : Finset (Finset (Fin 2)) := {∅, {0}, {0, 1}}

set_option maxRecDepth 4000 in

theorem rc58_box_mono_card :
    (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card = 2 := by
  rw [rc58_Amono, rc58_Bmono]; decide

set_option maxRecDepth 4000 in


theorem rc58_box_mono_compressed_card :
    (rc20_famCylBoxComp 2 (Down.compression 0 rc58_Amono) (Down.compression 0 rc58_Bmono)).card = 1 := by
  rw [rc58_Amono, rc58_Bmono]; decide

set_option maxRecDepth 4000 in





theorem rc58_box_strict_shrink :
    (rc20_famCylBoxComp 2 (Down.compression 0 rc58_Amono) (Down.compression 0 rc58_Bmono)).card
      < (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card := by
  rw [rc58_box_mono_compressed_card, rc58_box_mono_card]; norm_num

open Classical in





theorem rc58_boxCompressionMono_false : ¬ rc22_BoxCompressionMono := by
  intro h
  have hle := h 2 rc58_Amono rc58_Bmono 0
  have hstrict := rc58_box_strict_shrink
  rw [rc20_famCylBoxComp_eq, rc20_famCylBoxComp_eq] at hstrict
  exact absurd hle (not_le.mpr hstrict)

set_option maxRecDepth 4000 in



theorem rc58_wall_holds_on_monoCE :
    (rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card
      ≤ (rc20_reflInterComp 2 rc58_Amono rc58_Bmono).card := by
  rw [rc58_Amono, rc58_Bmono]; decide









open Classical in







theorem rc58_matching_iff_wall (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
      Nonempty ((rc20_famCylBox 𝒜 ℬ : Finset (Finset α)) ↪ (rc10_reflInter 𝒜 ℬ : Finset (Finset α))) := by
  rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_coe, Fintype.card_coe]













def rc58_kadm (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (rc20_reflInterComp n 𝒜 ℬ).filter (fun R => decide (∃ K ∈ (univ : Finset (Finset (Fin n))),
    rc20_traceClass n K S ⊆ 𝒜 ∧ R ∩ K = S ∩ K) = true)

open Classical in




theorem rc58_kadm_subset_reflInter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc58_kadm n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc58_kadm, Finset.mem_filter] at hR
  rw [← rc20_reflInterComp_eq]
  exact hR.1




def rc58_KadmSDR : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∃ f : Finset (Fin n) → Finset (Fin n),
      Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n))) ∧
      ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc58_kadm n 𝒜 ℬ S

open Classical in




theorem rc58_kadmSDR_closes_wall (h : rc58_KadmSDR) : rc20_FamCylBoxResidue := by
  intro n 𝒜 ℬ
  obtain ⟨f, hinj, hmem⟩ := h n 𝒜 ℬ
  refine Finset.card_le_card_of_injOn f (fun S hS => ?_) hinj
  exact rc58_kadm_subset_reflInter n 𝒜 ℬ S (hmem S hS)

open Classical in


theorem rc58_reimer_closes_of_kadmSDR (h : rc58_KadmSDR) : rc18_CylBoxReflInter :=
  rc20_cylBoxReflInter_of_famCylBoxResidue (rc58_kadmSDR_closes_wall h)

open Classical in






theorem rc58_kadm_hall_iff_sdr (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∀ 𝒮 : Finset (rc20_famCylBox 𝒜 ℬ),
        #𝒮 ≤ #(𝒮.biUnion (fun S => rc58_kadm n 𝒜 ℬ (S : Finset (Fin n))))) ↔
      ∃ f : (rc20_famCylBox 𝒜 ℬ) → Finset (Fin n),
        Function.Injective f ∧
          ∀ S : (rc20_famCylBox 𝒜 ℬ), f S ∈ rc58_kadm n 𝒜 ℬ (S : Finset (Fin n)) :=
  Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun S : (rc20_famCylBox 𝒜 ℬ) => rc58_kadm n 𝒜 ℬ (S : Finset (Fin n)))











def rc58_Arc57 : Finset (Finset (Fin 2)) := {∅, {0}, {1}}


def rc58_Brc57 : Finset (Finset (Fin 2)) := {{0}, {1}, {0, 1}}

set_option maxRecDepth 4000 in






theorem rc58_kadm_hall_holds_on_rc57pair :
    ∀ 𝒯 ∈ (rc20_famCylBoxComp 2 rc58_Arc57 rc58_Brc57).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc58_kadm 2 rc58_Arc57 rc58_Brc57)).card := by
  rw [rc58_Arc57, rc58_Brc57]; decide

set_option maxRecDepth 4000 in





theorem rc58_kadm_proper_on_rc57pair :
    (rc58_kadm 2 rc58_Arc57 rc58_Brc57 {0}).card
      < (rc20_reflInterComp 2 rc58_Arc57 rc58_Brc57).card := by
  rw [rc58_Arc57, rc58_Brc57]; decide



open Classical in




































theorem rc58_reimer_bipartiteFlow :
    (¬ rc22_BoxCompressionMono)
      ∧ ((rc20_famCylBoxComp 2 rc58_Amono rc58_Bmono).card
          ≤ (rc20_reflInterComp 2 rc58_Amono rc58_Bmono).card)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 2))),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
            Nonempty ((rc20_famCylBox 𝒜 ℬ : Finset (Finset (Fin 2)))
              ↪ (rc10_reflInter 𝒜 ℬ : Finset (Finset (Fin 2)))))
      ∧ (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
          rc58_kadm n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ)
      ∧ (rc58_KadmSDR → rc18_CylBoxReflInter)
      ∧ (∀ 𝒯 ∈ (rc20_famCylBoxComp 2 rc58_Arc57 rc58_Brc57).powerset,
          𝒯.card ≤ (𝒯.biUnion (rc58_kadm 2 rc58_Arc57 rc58_Brc57)).card)
      ∧ ((rc58_kadm 2 rc58_Arc57 rc58_Brc57 {0}).card
          < (rc20_reflInterComp 2 rc58_Arc57 rc58_Brc57).card) :=
  ⟨rc58_boxCompressionMono_false,
    rc58_wall_holds_on_monoCE,
    fun 𝒜 ℬ => rc58_matching_iff_wall 𝒜 ℬ,
    rc58_kadm_subset_reflInter,
    rc58_reimer_closes_of_kadmSDR,
    rc58_kadm_hall_holds_on_rc57pair,
    rc58_kadm_proper_on_rc57pair⟩

end StatMech.Walls
