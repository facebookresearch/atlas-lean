/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Code.Walls.rc22doublecover

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]













theorem rc23_compl_inter_eq_iff (U S K : Finset α) :
    Uᶜ ∩ K = Sᶜ ∩ K ↔ U ∩ K = S ∩ K := by
  constructor
  · intro h
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hxU, hxK⟩
      refine ⟨?_, hxK⟩
      by_contra hxS
      have : x ∈ Sᶜ ∩ K := Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hxS, hxK⟩
      rw [← h] at this
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp this).1) hxU
    · rintro ⟨hxS, hxK⟩
      refine ⟨?_, hxK⟩
      by_contra hxU
      have : x ∈ Uᶜ ∩ K := Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hxU, hxK⟩
      rw [h] at this
      exact (Finset.mem_compl.mp (Finset.mem_inter.mp this).1) hxS
  · intro h
    ext x
    simp only [Finset.mem_inter, Finset.mem_compl]
    constructor
    · rintro ⟨hxU, hxK⟩
      refine ⟨?_, hxK⟩
      intro hxS
      have : x ∈ S ∩ K := Finset.mem_inter.mpr ⟨hxS, hxK⟩
      rw [← h] at this
      exact hxU (Finset.mem_inter.mp this).1
    · rintro ⟨hxS, hxK⟩
      refine ⟨?_, hxK⟩
      intro hxU
      have : x ∈ U ∩ K := Finset.mem_inter.mpr ⟨hxU, hxK⟩
      rw [h] at this
      exact hxS (Finset.mem_inter.mp this).1





theorem rc23_traceCond_complFam (𝒜 : Finset (Finset α)) (K S : Finset α) :
    (∀ T : Finset α, T ∩ K = Sᶜ ∩ K → T ∈ rc22_complFam 𝒜)
      ↔ (∀ U : Finset α, U ∩ K = S ∩ K → U ∈ 𝒜) := by
  constructor
  · intro h U hU
    have := h Uᶜ ((rc23_compl_inter_eq_iff U S K).mpr hU)
    rw [rc22_mem_complFam, compl_compl] at this
    exact this
  · intro h T hT
    rw [rc22_mem_complFam]
    refine h Tᶜ ?_
    apply (rc23_compl_inter_eq_iff Tᶜ S K).mp
    rw [compl_compl]; exact hT

open Classical in




theorem rc23_mem_famCylBox_compl (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc20_famCylBox 𝒜 ℬ ↔
      Sᶜ ∈ rc20_famCylBox (rc22_complFam 𝒜) (rc22_complFam ℬ) := by
  rw [rc21_mem_famCylBox, rc21_mem_famCylBox]
  refine exists_congr fun K => exists_congr fun L => ?_
  rw [rc23_traceCond_complFam 𝒜 K S, rc23_traceCond_complFam ℬ L S]

open Classical in




theorem rc23_famCylBox_image_compl (𝒜 ℬ : Finset (Finset α)) :
    (rc20_famCylBox 𝒜 ℬ).image compl
      = rc20_famCylBox (rc22_complFam 𝒜) (rc22_complFam ℬ) := by
  ext R
  rw [rc22_mem_complImage]
  rw [rc23_mem_famCylBox_compl 𝒜 ℬ Rᶜ, compl_compl]

open Classical in



theorem rc23_card_famCylBox_complFam (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) = #(rc20_famCylBox (rc22_complFam 𝒜) (rc22_complFam ℬ)) := by
  rw [← rc23_famCylBox_image_compl, Finset.card_image_of_injective _ compl_injective]










theorem rc23_complFam_isUpperSet {𝒜 : Finset (Finset α)}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α))) :
    IsUpperSet (rc22_complFam 𝒜 : Set (Finset α)) := by
  intro T U hTU hT
  rw [Finset.mem_coe, rc22_mem_complFam] at hT ⊢
  exact h𝒜 (compl_le_compl hTU) hT







open Classical in





theorem rc23_card_reflInter_complFam (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter (rc22_complFam 𝒜) (rc22_complFam ℬ)) = #(rc10_reflInter 𝒜 ℬ) := by
  apply Finset.card_bij (fun S _ => Sᶜ)
  · intro S hS
    rw [rc20_mem_reflInter, rc22_mem_complFam, rc22_mem_complFam, compl_compl] at hS
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hS.1, hS.2⟩
  · intro S _ S' _ h
    exact compl_injective h
  · intro T hT
    rw [rc20_mem_reflInter] at hT
    refine ⟨Tᶜ, ?_, by rw [compl_compl]⟩
    rw [rc20_mem_reflInter, rc22_mem_complFam, rc22_mem_complFam, compl_compl]
    exact hT










open Classical in







theorem rc23_boxDownsetBase_proof {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset (Fin n)))) (hℬ : IsLowerSet (ℬ : Set (Finset (Fin n)))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc23_card_famCylBox_complFam 𝒜 ℬ, ← rc23_card_reflInter_complFam 𝒜 ℬ]
  exact rc22_famCylBox_le_reflInter_of_upperSet
    (rc23_complFam_isUpperSet h𝒜) (rc23_complFam_isUpperSet hℬ)



theorem rc23_boxDownsetBase : rc22_BoxDownsetBase :=
  fun _ _ _ h𝒜 hℬ => rc23_boxDownsetBase_proof h𝒜 hℬ
























theorem rc23_famCylBox_downDown_strictDecrease :
    #(rc20_famCylBox
        (Down.compression 0 ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))))
        (Down.compression 0 ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3)))))
      < #(rc20_famCylBox ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}})) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_famCylBoxComp_eq]
  decide





theorem rc23_boxCompressionMono_false : ¬ rc22_BoxCompressionMono := by
  intro h
  have hle := h 3 ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}})
    ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}}) 0
  exact absurd hle (not_le.mpr rc23_famCylBox_downDown_strictDecrease)










open Classical in




theorem rc23_wall_still_holds_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  rc20_famCylBox_fin2 𝒜 ℬ











theorem rc23_boxDownsetBase_strict_witness :
    #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {1}, {2}, {0,2}, {1,2}}))
      < #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 3)))
        ({∅, {0}, {1}, {2}, {0,2}, {1,2}})) := by
  rw [← rc20_famCylBoxComp_eq, ← rc20_reflInterComp_eq]
  decide



set_option linter.unusedVariables false in
open Classical in





























theorem rc23_reimer_boxmono :
    rc22_BoxDownsetBase
      ∧ (¬ rc22_BoxCompressionMono)
      ∧ (#(rc20_famCylBox
          (Down.compression 0 ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))))
          (Down.compression 0 ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3)))))
          < #(rc20_famCylBox ({{0}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3)))
          ({∅, {0}, {1}, {2}, {0,1}, {1,2}, {0,1,2}})))
      ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
          #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :=
  ⟨rc23_boxDownsetBase,
    rc23_boxCompressionMono_false,
    rc23_famCylBox_downDown_strictDecrease,
    rc23_wall_still_holds_fin2⟩

end StatMech.Walls
