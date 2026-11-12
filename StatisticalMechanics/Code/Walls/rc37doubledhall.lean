/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Code.Walls.rc36hallmarriage
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]

















def rc37_admLeft (n : ℕ) (𝒜 : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (R ∈ 𝒜 ∧
    ∃ K ∈ (univ : Finset (Finset (Fin n))), rc20_traceClass n K S ⊆ 𝒜 ∧ R ∩ K = S ∩ K) = true)



def rc37_rightMem (n : ℕ) (ℬ : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  univ.filter (fun R => decide (Rᶜ ∈ ℬ) = true)










theorem rc37_admOneSidedA_eq_inter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ rc37_rightMem n ℬ := by
  ext R
  rw [rc33_admOneSidedA, rc37_admLeft, rc37_rightMem, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq,
    decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hRA, hRB, K, hK, hKA, hRK⟩
    exact ⟨⟨Finset.mem_univ _, hRA, K, hK, hKA, hRK⟩, ⟨Finset.mem_univ _, hRB⟩⟩
  · rintro ⟨⟨_, hRA, K, hK, hKA, hRK⟩, ⟨_, hRB⟩⟩
    exact ⟨Finset.mem_univ _, hRA, hRB, K, hK, hKA, hRK⟩






theorem rc37_rightMem_indep (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S S' : Finset (Fin n)) :
    ∃ RM : Finset (Finset (Fin n)),
      rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ RM ∧
      rc33_admOneSidedA n 𝒜 ℬ S' = rc37_admLeft n 𝒜 S' ∩ RM :=
  ⟨rc37_rightMem n ℬ, rc37_admOneSidedA_eq_inter n 𝒜 ℬ S, rc37_admOneSidedA_eq_inter n 𝒜 ℬ S'⟩












noncomputable def rc37_complBoxDoubled (𝒜 ℬ : Finset (Finset α)) : Finset (Finset (α ⊕ α)) :=
  (rc10_reflInter 𝒜 ℬ).image (fun R => dbl R Rᶜ)



theorem rc37_dblCompl_mem_boxDoubled (𝒜 ℬ : Finset (Finset α)) {R : Finset α}
    (hR : R ∈ rc10_reflInter 𝒜 ℬ) : dbl R Rᶜ ∈ boxDoubled 𝒜 ℬ := by
  rw [rc20_mem_reflInter] at hR
  rw [mem_boxDoubled]
  exact ⟨R, hR.1, Rᶜ, hR.2, disjoint_compl_right, rfl⟩




theorem rc37_dblCompl_injOn (s : Set (Finset α)) :
    Set.InjOn (fun R : Finset α => dbl R Rᶜ) s := by
  intro R _ R' _ h
  have := dbl_injective (a₁ := (R, Rᶜ)) (a₂ := (R', R'ᶜ)) h
  exact (Prod.mk.injEq _ _ _ _ ▸ this).1



theorem rc37_complBoxDoubled_subset (𝒜 ℬ : Finset (Finset α)) :
    rc37_complBoxDoubled 𝒜 ℬ ⊆ boxDoubled 𝒜 ℬ := by
  intro U hU
  rw [rc37_complBoxDoubled, Finset.mem_image] at hU
  obtain ⟨R, hR, rfl⟩ := hU
  exact rc37_dblCompl_mem_boxDoubled 𝒜 ℬ hR





theorem rc37_complBoxDoubled_card_eq_reflInter (𝒜 ℬ : Finset (Finset α)) :
    (rc37_complBoxDoubled 𝒜 ℬ).card = (rc10_reflInter 𝒜 ℬ).card := by
  rw [rc37_complBoxDoubled]
  exact Finset.card_image_of_injOn (rc37_dblCompl_injOn _)














noncomputable def rc37_admDoubled (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    Finset (Finset (Fin n ⊕ Fin n)) :=
  (rc33_admOneSidedA n 𝒜 ℬ S).image (fun R => dbl R Rᶜ)




theorem rc37_admDoubled_subset_boxDoubled (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc37_admDoubled n 𝒜 ℬ S ⊆ boxDoubled 𝒜 ℬ := by
  intro U hU
  rw [rc37_admDoubled, Finset.mem_image] at hU
  obtain ⟨R, hR, rfl⟩ := hU
  exact rc37_dblCompl_mem_boxDoubled 𝒜 ℬ
    (rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ S hR)

open Classical in






theorem rc37_biUnion_admDoubled_card (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) :
    (𝒯.biUnion (rc37_admDoubled n 𝒜 ℬ)).card
      = (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := by
  have hcomm : 𝒯.biUnion (rc37_admDoubled n 𝒜 ℬ)
      = (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).image (fun R => dbl R Rᶜ) := by
    rw [Finset.biUnion_image]; rfl
  rw [hcomm]
  refine Finset.card_image_of_injOn ?_
  intro R hR R' hR' h
  have := dbl_injective (a₁ := (R, Rᶜ)) (a₂ := (R', R'ᶜ)) h
  exact (Prod.mk.injEq _ _ _ _ ▸ this).1






def rc37_HallDoubled : Prop :=
  ∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))),
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled n 𝒜 ℬ)).card

open Classical in





theorem rc37_hallDoubled_iff_hallOneSidedA :
    rc37_HallDoubled ↔ rc33_HallOneSidedA := by
  constructor
  · intro h n 𝒜 ℬ 𝒯 h𝒯
    have := h n 𝒜 ℬ 𝒯 h𝒯
    rwa [rc37_biUnion_admDoubled_card] at this
  · intro h n 𝒜 ℬ 𝒯 h𝒯
    have := h n 𝒜 ℬ 𝒯 h𝒯
    rwa [rc37_biUnion_admDoubled_card]

open Classical in


theorem rc37_famCylBoxResidue_of_hallDoubled (h : rc37_HallDoubled) :
    rc20_FamCylBoxResidue :=
  rc33_famCylBoxResidue_of_hallOneSidedA (rc37_hallDoubled_iff_hallOneSidedA.mp h)

open Classical in





theorem rc37_reimer_closes_of_hallDoubled (h : rc37_HallDoubled) :
    rc18_CylBoxReflInter :=
  rc33_reimer_closes_of_hallOneSidedA (rc37_hallDoubled_iff_hallOneSidedA.mp h)










open Classical in




theorem rc37_hallDoubled_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 2 𝒜 ℬ)).card := by
  intro 𝒯 h𝒯
  rw [rc37_biUnion_admDoubled_card]
  exact rc33_hallOneSidedA_prop_of_bool 2 𝒜 ℬ (rc33_hallOneSidedA_fin2 𝒜 ℬ) 𝒯 h𝒯

open Classical in







theorem rc37_hallDoubled_fin3_refuter :
    ∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 3 rc32_A3 rc32_B3)).card := by
  intro 𝒯 h𝒯
  rw [rc37_biUnion_admDoubled_card]
  exact rc33_hallOneSidedA_prop_of_bool 3 rc32_A3 rc32_B3 rc33_hallOneSidedA_fin3_refuter 𝒯 h𝒯








set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in






theorem rc37_admDoubled_proper_fin3 :
    (rc37_admDoubled 3 rc32_A3 rc32_B3 {1}).card
      < (boxDoubled rc32_A3 rc32_B3).card := by
  have hle : (rc37_admDoubled 3 rc32_A3 rc32_B3 {1}).card
      = (rc33_admOneSidedA 3 rc32_A3 rc32_B3 {1}).card := by
    rw [rc37_admDoubled]
    exact Finset.card_image_of_injOn (rc37_dblCompl_injOn _)
  rw [hle, card_boxDoubled]
  rw [rc32_A3, rc32_B3]
  decide



set_option linter.unusedVariables false in
open Classical in




































theorem rc37_reimer_doubledhall :
    (∀ (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)),
        rc33_admOneSidedA n 𝒜 ℬ S = rc37_admLeft n 𝒜 S ∩ rc37_rightMem n ℬ)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          (rc37_complBoxDoubled 𝒜 ℬ).card = (rc10_reflInter 𝒜 ℬ).card
            ∧ rc37_complBoxDoubled 𝒜 ℬ ⊆ boxDoubled 𝒜 ℬ)
      ∧ (rc37_HallDoubled ↔ rc33_HallOneSidedA)
      ∧ (rc37_HallDoubled → rc18_CylBoxReflInter)
      ∧ (∀ 𝒯 ∈ (rc20_famCylBox rc32_A3 rc32_B3).powerset,
          𝒯.card ≤ (𝒯.biUnion (rc37_admDoubled 3 rc32_A3 rc32_B3)).card)
      ∧ ((rc37_admDoubled 3 rc32_A3 rc32_B3 {1}).card
          < (boxDoubled rc32_A3 rc32_B3).card) :=
  ⟨fun n 𝒜 ℬ S => rc37_admOneSidedA_eq_inter n 𝒜 ℬ S,
    fun 𝒜 ℬ => ⟨rc37_complBoxDoubled_card_eq_reflInter 𝒜 ℬ, rc37_complBoxDoubled_subset 𝒜 ℬ⟩,
    rc37_hallDoubled_iff_hallOneSidedA,
    rc37_reimer_closes_of_hallDoubled,
    rc37_hallDoubled_fin3_refuter,
    rc37_admDoubled_proper_fin3⟩

end StatMech.Walls
