/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Code.Walls.rc37doubledhall
import Code.Inequalities.ReimerDoubled
import Code.Inequalities.ReimerButterflyStep

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]









omit [Fintype α] in





theorem rc38_doubleCompress_boxDoubled_card (i : α)
    (𝒜 ℬ : Finset (Finset α)) :
    (doubleCompress i (boxDoubled 𝒜 ℬ)).card = (boxDoubled 𝒜 ℬ).card :=
  doubleCompress_card i (boxDoubled 𝒜 ℬ)



















theorem rc38_reflInter_le_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    (rc10_reflInter 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card := by
  rw [← rc37_complBoxDoubled_card_eq_reflInter]
  exact Finset.card_le_card (rc37_complBoxDoubled_subset 𝒜 ℬ)

omit [Fintype α] in



theorem rc38_boxDoubled_card_eq_dpairsCount (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ :=
  card_boxDoubled_eq_dpairsCount 𝒜 ℬ














theorem rc38_boxDoubled_singletonEmpty_fin1 :
    (boxDoubled ({∅} : Finset (Finset (Fin 1))) ({∅})).card = 1 := by
  rw [rc38_boxDoubled_card_eq_dpairsCount]; decide




theorem rc38_reflInter_singletonEmpty_fin1 :
    (rc10_reflInter ({∅} : Finset (Finset (Fin 1))) ({∅})).card = 0 := by
  rw [← rc20_reflInterComp_eq]; decide








theorem rc38_boxDoubled_le_reflInter_false :
    ¬ (∀ (𝒜 ℬ : Finset (Finset (Fin 1))),
        (boxDoubled 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card) := by
  intro h
  have := h ({∅}) ({∅})
  rw [rc38_boxDoubled_singletonEmpty_fin1, rc38_reflInter_singletonEmpty_fin1] at this
  omega





theorem rc38_boxDoubled_le_reflInter_false_fin3 :
    ¬ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        (boxDoubled 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card) := by
  intro h
  have hbd : (boxDoubled ({∅} : Finset (Finset (Fin 3))) ({∅})).card = 1 := by
    rw [rc38_boxDoubled_card_eq_dpairsCount]; decide
  have hri : (rc10_reflInter ({∅} : Finset (Finset (Fin 3))) ({∅})).card = 0 := by
    rw [← rc20_reflInterComp_eq]; decide
  have := h ({∅}) ({∅})
  rw [hbd, hri] at this
  omega












omit [Fintype α] in



theorem rc38_insert_inr_dbl (S T : Finset α) (i : α) :
    insert (Sum.inr i) (dbl S T) = dbl S (insert i T) := by
  ext x
  cases x with
  | inl a => simp [mem_dbl_inl]
  | inr a => simp [mem_dbl_inr, Finset.mem_insert]




theorem rc38_boxDoubled_isDownAtLeft_cex :
    IsDownAtLeft (0 : Fin 1) (boxDoubled ({∅}) ({∅, {0}})) := by
  intro s hs
  rw [mem_boxDoubled] at hs
  obtain ⟨S, hS, T, hT, hd, rfl⟩ := hs
  have hSempty : S = ∅ := by simpa using hS
  subst hSempty
  have hnot : Sum.inl (0 : Fin 1) ∉ dbl (∅ : Finset (Fin 1)) T := by rw [mem_dbl_inl]; simp
  rw [Finset.erase_eq_of_notMem hnot, mem_boxDoubled]
  exact ⟨∅, hS, T, hT, hd, rfl⟩




theorem rc38_boxDoubled_isUpAtRight_cex :
    IsUpAtRight (0 : Fin 1) (boxDoubled ({∅}) ({∅, {0}} : Finset (Finset (Fin 1)))) := by
  intro s hs
  rw [mem_boxDoubled] at hs
  obtain ⟨S, hS, T, hT, hd, rfl⟩ := hs
  have hSempty : S = ∅ := by simpa using hS
  subst hSempty
  rw [rc38_insert_inr_dbl, mem_boxDoubled]
  refine ⟨∅, hS, insert 0 T, ?_, Finset.disjoint_empty_left _, rfl⟩
  fin_cases hT <;> decide





theorem rc38_boxDoubled_doubleCompress_fixed_cex :
    doubleCompress (0 : Fin 1) (boxDoubled ({∅}) ({∅, {0}}))
      = boxDoubled ({∅}) ({∅, {0}}) :=
  doubleCompress_eq_self 0 rc38_boxDoubled_isDownAtLeft_cex rc38_boxDoubled_isUpAtRight_cex



theorem rc38_dblEmpty_mem_boxDoubled_cex :
    dbl (∅ : Finset (Fin 1)) ∅ ∈ boxDoubled ({∅}) ({∅, {0}}) := by
  rw [mem_boxDoubled]
  exact ⟨∅, by simp, ∅, by simp, Finset.disjoint_empty_left _, rfl⟩





theorem rc38_dblEmpty_notMem_complBoxDoubled_cex :
    dbl (∅ : Finset (Fin 1)) ∅ ∉ rc37_complBoxDoubled ({∅}) ({∅, {0}}) := by
  rw [rc37_complBoxDoubled, Finset.mem_image]
  rintro ⟨R, _hR, hRdbl⟩
  have hinj := dbl_injective (a₁ := (R, Rᶜ)) (a₂ := ((∅ : Finset (Fin 1)), ∅)) hRdbl
  have hRe : R = ∅ := (Prod.mk.injEq _ _ _ _ ▸ hinj).1
  have hRc : Rᶜ = ∅ := (Prod.mk.injEq _ _ _ _ ▸ hinj).2
  have huniv : R = Finset.univ := by rw [← compl_compl R, hRc, compl_empty]
  rw [hRe] at huniv
  exact absurd huniv.symm (by decide)









theorem rc38_fixed_boxDoubled_not_cubefilling :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 1))) (i : Fin 1) (U : Finset (Fin 1 ⊕ Fin 1)),
      doubleCompress i (boxDoubled 𝒜 ℬ) = boxDoubled 𝒜 ℬ ∧
      U ∈ boxDoubled 𝒜 ℬ ∧ U ∉ rc37_complBoxDoubled 𝒜 ℬ :=
  ⟨{∅}, {∅, {0}}, 0, dbl ∅ ∅, rc38_boxDoubled_doubleCompress_fixed_cex,
    rc38_dblEmpty_mem_boxDoubled_cex, rc38_dblEmpty_notMem_complBoxDoubled_cex⟩













open Classical in





theorem rc38_reimer_of_hallDoubled (h : rc37_HallDoubled) : rc18_CylBoxReflInter :=
  rc37_reimer_closes_of_hallDoubled h

open Classical in




theorem rc38_famCylBoxResidue_of_hallDoubled (h : rc37_HallDoubled) : rc20_FamCylBoxResidue :=
  rc37_famCylBoxResidue_of_hallDoubled h



open Classical in





































theorem rc38_reimer_butterfly_deadend :
    (∀ (i : Fin 1) (𝒜 ℬ : Finset (Finset (Fin 1))),
        (doubleCompress i (boxDoubled 𝒜 ℬ)).card = (boxDoubled 𝒜 ℬ).card)
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          (rc10_reflInter 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card)
      ∧ (¬ (∀ (𝒜 ℬ : Finset (Finset (Fin 1))),
          (boxDoubled 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card))
      ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 1))) (i : Fin 1) (U : Finset (Fin 1 ⊕ Fin 1)),
          doubleCompress i (boxDoubled 𝒜 ℬ) = boxDoubled 𝒜 ℬ ∧
          U ∈ boxDoubled 𝒜 ℬ ∧ U ∉ rc37_complBoxDoubled 𝒜 ℬ)
      ∧ (rc37_HallDoubled → rc18_CylBoxReflInter)
      ∧ (rc37_HallDoubled → rc20_FamCylBoxResidue) :=
  ⟨fun i 𝒜 ℬ => rc38_doubleCompress_boxDoubled_card i 𝒜 ℬ,
    fun 𝒜 ℬ => rc38_reflInter_le_boxDoubled 𝒜 ℬ,
    rc38_boxDoubled_le_reflInter_false,
    rc38_fixed_boxDoubled_not_cubefilling,
    rc38_reimer_of_hallDoubled,
    rc38_famCylBoxResidue_of_hallDoubled⟩

end StatMech.Walls
