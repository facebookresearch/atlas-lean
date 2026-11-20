/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































































import Code.Walls.rc52pairimage
import Code.Walls.rc46butterfly
import Code.Walls.rc38butterflymono
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










open Classical in




noncomputable def rc53_boxWithWitness (𝒜 ℬ : Finset (Finset α)) : Finset (Finset (α ⊕ α)) :=
  rc46_famCylBoxDoubled 𝒜 ℬ



theorem rc53_boxWithWitness_eq_famCylBoxDoubled (𝒜 ℬ : Finset (Finset α)) :
    rc53_boxWithWitness 𝒜 ℬ = rc46_famCylBoxDoubled 𝒜 ℬ := rfl

open Classical in




theorem rc53_boxWithWitness_card (𝒜 ℬ : Finset (Finset α)) :
    (rc53_boxWithWitness 𝒜 ℬ).card = (rc20_famCylBox 𝒜 ℬ).card :=
  rc46_famCylBoxDoubled_card_eq 𝒜 ℬ













def rc53_isCubeFilling {n : ℕ} (U : Finset (Fin n ⊕ Fin n)) : Prop :=
  (univ.filter (fun i => Sum.inl i ∈ U))
    = (univ.filter (fun i => Sum.inr i ∈ U))ᶜ

instance {n : ℕ} : DecidablePred (rc53_isCubeFilling (n := n)) :=
  fun _ => by unfold rc53_isCubeFilling; infer_instance




def rc53_cubeFillCount {n : ℕ} (F : Finset (Finset (Fin n ⊕ Fin n))) : ℕ :=
  (F.filter rc53_isCubeFilling).card



theorem rc53_dbl_compl_isCubeFilling {n : ℕ} (R : Finset (Fin n)) :
    rc53_isCubeFilling (dbl R Rᶜ) := by
  unfold rc53_isCubeFilling
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, mem_dbl_inl,
    mem_dbl_inr]
  tauto

open Classical in



theorem rc53_boxWithWitness_all_cubeFilling {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n)))
    {U : Finset (Fin n ⊕ Fin n)} (hU : U ∈ rc53_boxWithWitness 𝒜 ℬ) :
    rc53_isCubeFilling U := by
  rw [rc53_boxWithWitness, rc46_famCylBoxDoubled, Finset.mem_image] at hU
  obtain ⟨S, _, rfl⟩ := hU
  exact rc53_dbl_compl_isCubeFilling S

open Classical in





theorem rc53_cubeFillCount_boxWithWitness {n : ℕ} (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc53_cubeFillCount (rc53_boxWithWitness 𝒜 ℬ) = (rc20_famCylBox 𝒜 ℬ).card := by
  unfold rc53_cubeFillCount
  rw [Finset.filter_true_of_mem (fun U hU => rc53_boxWithWitness_all_cubeFilling 𝒜 ℬ hU)]
  exact rc53_boxWithWitness_card 𝒜 ℬ












theorem rc53_doubleCompress_boxWithWitness_card (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (doubleCompress i (rc53_boxWithWitness 𝒜 ℬ)).card = (rc53_boxWithWitness 𝒜 ℬ).card :=
  doubleCompress_card i (rc53_boxWithWitness 𝒜 ℬ)











open Classical in




theorem rc53_boxWithWitness_eq_comp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc53_boxWithWitness 𝒜 ℬ
      = (rc20_famCylBoxComp n 𝒜 ℬ).image (fun S => dbl S Sᶜ) := by
  rw [rc53_boxWithWitness, rc46_famCylBoxDoubled, rc20_famCylBoxComp_eq]




theorem rc53_cubeFillCount_eq_comp {n : ℕ} (F : Finset (Finset (Fin n ⊕ Fin n))) :
    rc53_cubeFillCount F
      = (F.filter (fun U => decide ((univ.filter (fun i => Sum.inl i ∈ U))
          = (univ.filter (fun i => Sum.inr i ∈ U))ᶜ) = true)).card := by
  unfold rc53_cubeFillCount rc53_isCubeFilling
  congr 1
  apply Finset.filter_congr
  intro U _
  rw [decide_eq_true_eq]

set_option maxRecDepth 10000 in












theorem rc53_cubeFillCount_strictly_decreases_fin3 :
    rc53_cubeFillCount (doubleCompress 1 (rc53_boxWithWitness rc46_Adn rc46_Bdn))
      < rc53_cubeFillCount (rc53_boxWithWitness rc46_Adn rc46_Bdn) := by
  rw [rc53_boxWithWitness_eq_comp, rc53_cubeFillCount_eq_comp, rc53_cubeFillCount_eq_comp,
    rc46_Adn, rc46_Bdn]
  decide







theorem rc53_boxMonotonisation_functional_refuted :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 3))) (i : Fin 3),
      rc53_cubeFillCount (doubleCompress i (rc53_boxWithWitness 𝒜 ℬ))
        < rc53_cubeFillCount (rc53_boxWithWitness 𝒜 ℬ) :=
  ⟨rc46_Adn, rc46_Bdn, 1, rc53_cubeFillCount_strictly_decreases_fin3⟩










open Classical in





theorem rc53_cubeFillCount_le_reflInter_at_increasing {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    rc53_cubeFillCount (rc53_boxWithWitness (eventFamily A) (eventFamily B))
      ≤ (rc10_reflInter (eventFamily A) (eventFamily B)).card := by
  rw [rc53_cubeFillCount_boxWithWitness]
  exact rc20_famCylBox_of_increasing hA hB










omit [Fintype α] in



theorem rc53_doubleCompress_dpairsCount_invariant (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (doubleCompress i (boxDoubled 𝒜 ℬ)).card = (boxDoubled 𝒜 ℬ).card :=
  doubleCompress_card i (boxDoubled 𝒜 ℬ)





theorem rc53_dpairsCount_wrong_side (𝒜 ℬ : Finset (Finset α)) :
    (rc10_reflInter 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card :=
  rc38_reflInter_le_boxDoubled 𝒜 ℬ








open Classical in


theorem rc53_reimer_of_hallDoubled (h : rc37_HallDoubled) : rc18_CylBoxReflInter :=
  rc37_reimer_closes_of_hallDoubled h

open Classical in


theorem rc53_famCylBoxResidue_of_hallDoubled (h : rc37_HallDoubled) : rc20_FamCylBoxResidue :=
  rc37_famCylBoxResidue_of_hallDoubled h

set_option maxRecDepth 4000 in




theorem rc53_wall_holds_on_refuter :
    (rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card
      ≤ (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card := by
  rw [rc46_Adn, rc46_Bdn]; decide



open Classical in


































theorem rc53_reimer_boxWithWitness_refuted :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        rc53_cubeFillCount (rc53_boxWithWitness 𝒜 ℬ) = (rc20_famCylBox 𝒜 ℬ).card)
      ∧ (∀ (i : Fin 3) (𝒜 ℬ : Finset (Finset (Fin 3))),
          (doubleCompress i (rc53_boxWithWitness 𝒜 ℬ)).card = (rc53_boxWithWitness 𝒜 ℬ).card)
      ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 3))) (i : Fin 3),
          rc53_cubeFillCount (doubleCompress i (rc53_boxWithWitness 𝒜 ℬ))
            < rc53_cubeFillCount (rc53_boxWithWitness 𝒜 ℬ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          (rc10_reflInter 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card)
      ∧ (rc37_HallDoubled → rc18_CylBoxReflInter)
      ∧ ((rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card
          ≤ (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card) :=
  ⟨fun 𝒜 ℬ => rc53_cubeFillCount_boxWithWitness 𝒜 ℬ,
    fun i 𝒜 ℬ => rc53_doubleCompress_boxWithWitness_card i 𝒜 ℬ,
    rc53_boxMonotonisation_functional_refuted,
    fun 𝒜 ℬ => rc53_dpairsCount_wrong_side 𝒜 ℬ,
    rc53_reimer_of_hallDoubled,
    rc53_wall_holds_on_refuter⟩

end StatMech.Walls
