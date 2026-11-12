/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Code.Walls.rc54weighted
import Code.Walls.rc46butterfly
import Code.Walls.rc38butterflymono
import Code.Walls.rc22doublecover
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]
















theorem rc55_famCylBox_downDown_strictly_decreases_fin3 :
    #(rc20_famCylBox (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn))
      < #(rc20_famCylBox rc46_Adn rc46_Bdn) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  exact rc46_downDownStep_decreases_famCylBox_fin3









theorem rc55_boxCompressionMono_false : ¬ rc22_BoxCompressionMono := by
  intro h
  have := h 3 rc46_Adn rc46_Bdn 1
  exact absurd this (not_le.mpr rc55_famCylBox_downDown_strictly_decreases_fin3)
















def rc55_leftProj (U : Finset (α ⊕ α)) : Finset α :=
  univ.filter (fun a => Sum.inl a ∈ U)


def rc55_rightProj (U : Finset (α ⊕ α)) : Finset α :=
  univ.filter (fun a => Sum.inr a ∈ U)


def rc55_isSuperfill (U : Finset (α ⊕ α)) : Prop :=
  rc55_leftProj U ∪ rc55_rightProj U = univ

instance : DecidablePred (rc55_isSuperfill (α := α)) :=
  fun _ => by unfold rc55_isSuperfill; infer_instance




def rc55_superfillCount (F : Finset (Finset (α ⊕ α))) : ℕ :=
  (F.filter rc55_isSuperfill).card


theorem rc55_leftProj_dbl (S T : Finset α) : rc55_leftProj (dbl S T) = S := by
  ext a
  simp only [rc55_leftProj, Finset.mem_filter, Finset.mem_univ, true_and, mem_dbl_inl]


theorem rc55_rightProj_dbl (S T : Finset α) : rc55_rightProj (dbl S T) = T := by
  ext a
  simp only [rc55_rightProj, Finset.mem_filter, Finset.mem_univ, true_and, mem_dbl_inr]


theorem rc55_dbl_compl_isSuperfill (R : Finset α) : rc55_isSuperfill (dbl R Rᶜ) := by
  unfold rc55_isSuperfill
  rw [rc55_leftProj_dbl, rc55_rightProj_dbl, Finset.union_compl]




theorem rc55_disjoint_fill_iff_compl {S T : Finset α} (hd : Disjoint S T) :
    S ∪ T = univ ↔ T = Sᶜ := by
  constructor
  · intro hu; exact (rc22_compl_of_disjoint_union hd hu).symm
  · rintro rfl; exact Finset.union_compl S

open Classical in




theorem rc55_superfill_filter_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).filter rc55_isSuperfill = rc37_complBoxDoubled 𝒜 ℬ := by
  ext U
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hU, hsf⟩
    rw [mem_boxDoubled] at hU
    obtain ⟨S, hS, T, hT, hd, rfl⟩ := hU
    have hfill : S ∪ T = univ := by
      unfold rc55_isSuperfill at hsf
      rwa [rc55_leftProj_dbl, rc55_rightProj_dbl] at hsf
    have hTc : T = Sᶜ := (rc55_disjoint_fill_iff_compl hd).mp hfill
    subst hTc
    rw [rc37_complBoxDoubled, Finset.mem_image]
    exact ⟨S, by rw [rc20_mem_reflInter]; exact ⟨hS, hT⟩, rfl⟩
  · intro hU
    rw [rc37_complBoxDoubled, Finset.mem_image] at hU
    obtain ⟨R, hR, rfl⟩ := hU
    exact ⟨rc37_complBoxDoubled_subset 𝒜 ℬ (by
      rw [rc37_complBoxDoubled, Finset.mem_image]; exact ⟨R, hR, rfl⟩),
      rc55_dbl_compl_isSuperfill R⟩

open Classical in






theorem rc55_superfillCount_boxDoubled_eq_reflInter (𝒜 ℬ : Finset (Finset α)) :
    rc55_superfillCount (boxDoubled 𝒜 ℬ) = #(rc10_reflInter 𝒜 ℬ) := by
  unfold rc55_superfillCount
  rw [rc55_superfill_filter_boxDoubled, rc37_complBoxDoubled_card_eq_reflInter]












theorem rc55_superfillCount_refuter_start :
    rc55_superfillCount (boxDoubled rc46_Adn rc46_Bdn) = 2 := by
  rw [rc46_Adn, rc46_Bdn]; decide





theorem rc55_superfillCount_refuter_step :
    rc55_superfillCount (doubleCompress 1 (boxDoubled rc46_Adn rc46_Bdn)) = 3 := by
  rw [rc46_Adn, rc46_Bdn]; decide




theorem rc55_superfill_nondecreasing_witness :
    rc55_superfillCount (boxDoubled rc46_Adn rc46_Bdn)
      ≤ rc55_superfillCount (doubleCompress 1 (boxDoubled rc46_Adn rc46_Bdn)) := by
  rw [rc55_superfillCount_refuter_start, rc55_superfillCount_refuter_step]; norm_num

















theorem rc55_reflInter_le_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) ≤ #(boxDoubled 𝒜 ℬ) :=
  rc38_reflInter_le_boxDoubled 𝒜 ℬ












open Classical in

theorem rc55_boxDownsetBase_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc22_boxDownsetBase_fin0 𝒜 ℬ

open Classical in

theorem rc55_boxDownsetBase_upperSet {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n)))) (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc22_boxDownsetBase_upperSet h𝒜 hℬ







open Classical in



theorem rc55_reimer_of_hallDoubled (h : rc37_HallDoubled) : rc18_CylBoxReflInter :=
  rc54_reimer_of_hallDoubled h

open Classical in

theorem rc55_famCylBoxResidue_of_hallDoubled (h : rc37_HallDoubled) : rc20_FamCylBoxResidue :=
  rc54_famCylBoxResidue_of_hallDoubled h

open Classical in



theorem rc55_reimerWprobCore_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) : ReimerWprobCore :=
  rc54_reimerWprobCore_of_famCylBoxResidue h





theorem rc55_wall_holds_on_refuter :
    (rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card
      ≤ (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card := by
  rw [rc46_Adn, rc46_Bdn]; decide



open Classical in









































theorem rc55_reimer_nonproduct :
    (¬ rc22_BoxCompressionMono)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          rc55_superfillCount (boxDoubled 𝒜 ℬ) = #(rc10_reflInter 𝒜 ℬ))
      ∧ (rc55_superfillCount (boxDoubled rc46_Adn rc46_Bdn)
          ≤ rc55_superfillCount (doubleCompress 1 (boxDoubled rc46_Adn rc46_Bdn)))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          #(rc10_reflInter 𝒜 ℬ) ≤ #(boxDoubled 𝒜 ℬ))
      ∧ (rc37_HallDoubled → rc18_CylBoxReflInter)
      ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) :=
  ⟨rc55_boxCompressionMono_false,
    fun 𝒜 ℬ => rc55_superfillCount_boxDoubled_eq_reflInter 𝒜 ℬ,
    rc55_superfill_nondecreasing_witness,
    fun 𝒜 ℬ => rc55_reflInter_le_boxDoubled 𝒜 ℬ,
    rc55_reimer_of_hallDoubled,
    rc55_reimerWprobCore_of_famCylBoxResidue⟩

end StatMech.Walls
