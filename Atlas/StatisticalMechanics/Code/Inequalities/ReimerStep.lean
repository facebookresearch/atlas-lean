/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Code.Inequalities.ReimerCompression
import Mathlib.Data.Finset.Prod

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [DecidableEq α]












noncomputable def boxFamily (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).image (fun p => p.1 ∪ p.2)



lemma mem_boxFamily (𝒜 ℬ : Finset (Finset α)) (U : Finset α) :
    U ∈ boxFamily 𝒜 ℬ ↔ ∃ S ∈ 𝒜, ∃ T ∈ ℬ, Disjoint S T ∧ S ∪ T = U := by
  unfold boxFamily
  simp only [mem_image, mem_filter, mem_product, Prod.exists]
  constructor
  · rintro ⟨S, T, ⟨⟨hS, hT⟩, hd⟩, rfl⟩; exact ⟨S, hS, T, hT, hd, rfl⟩
  · rintro ⟨S, hS, T, hT, hd, rfl⟩; exact ⟨S, T, ⟨⟨hS, hT⟩, hd⟩, rfl⟩


lemma boxFamily_comm (𝒜 ℬ : Finset (Finset α)) : boxFamily 𝒜 ℬ = boxFamily ℬ 𝒜 := by
  ext U
  simp only [mem_boxFamily]
  constructor
  · rintro ⟨S, hS, T, hT, hd, rfl⟩; exact ⟨T, hT, S, hS, hd.symm, union_comm T S⟩
  · rintro ⟨S, hS, T, hT, hd, rfl⟩; exact ⟨T, hT, S, hS, hd.symm, union_comm T S⟩


lemma boxFamily_mono {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ 𝒜') (hℬ : ℬ ⊆ ℬ') :
    boxFamily 𝒜 ℬ ⊆ boxFamily 𝒜' ℬ' := by
  intro U hU
  rw [mem_boxFamily] at hU ⊢
  obtain ⟨S, hS, T, hT, hd, hU⟩ := hU
  exact ⟨S, h𝒜 hS, T, hℬ hT, hd, hU⟩


@[simp] lemma boxFamily_empty_left (ℬ : Finset (Finset α)) : boxFamily ∅ ℬ = ∅ := by
  ext U; simp [mem_boxFamily]


@[simp] lemma boxFamily_empty_right (𝒜 : Finset (Finset α)) : boxFamily 𝒜 ∅ = ∅ := by
  ext U; simp [mem_boxFamily]










theorem boxFamily_card_le_mul (𝒜 ℬ : Finset (Finset α)) :
    (boxFamily 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card := by
  unfold boxFamily
  calc (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).image (fun p => p.1 ∪ p.2)).card
      ≤ ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card := card_image_le
    _ ≤ (𝒜 ×ˢ ℬ).card := card_filter_le _ _
    _ = 𝒜.card * ℬ.card := card_product _ _











theorem boxFamily_filter_notMem_coord (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (boxFamily 𝒜 ℬ).filter (fun U => i ∉ U)
      = boxFamily (𝒜.filter (fun S => i ∉ S)) (ℬ.filter (fun T => i ∉ T)) := by
  ext U
  simp only [mem_filter, mem_boxFamily, mem_filter]
  constructor
  · rintro ⟨⟨S, hS, T, hT, hd, rfl⟩, hiU⟩
    rw [mem_union, not_or] at hiU
    exact ⟨S, ⟨hS, hiU.1⟩, T, ⟨hT, hiU.2⟩, hd, rfl⟩
  · rintro ⟨S, ⟨hS, hiS⟩, T, ⟨hT, hiT⟩, hd, rfl⟩
    refine ⟨⟨S, hS, T, hT, hd, rfl⟩, ?_⟩
    rw [mem_union, not_or]; exact ⟨hiS, hiT⟩












def IsDownAtCoord (i : α) (𝒜 : Finset (Finset α)) : Prop := ∀ s ∈ 𝒜, s.erase i ∈ 𝒜


theorem downCompressFamily_eq_self_of_isDownAt (i : α) {𝒜 : Finset (Finset α)}
    (h : IsDownAtCoord i 𝒜) : Down.compression i 𝒜 = 𝒜 := by
  ext s
  rw [Down.mem_compression]
  constructor
  · rintro (⟨hs, _⟩ | ⟨hns, hins⟩)
    · exact hs
    · by_cases hi : i ∈ s
      · rw [insert_eq_of_mem hi] at hins; exact absurd hins hns
      · have := h _ hins; rw [erase_insert hi] at this; exact absurd this hns
  · intro hs; exact Or.inl ⟨hs, h _ hs⟩




theorem boxFamily_downCompress_eq_of_isDownAt (i : α) {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsDownAtCoord i 𝒜) (hℬ : IsDownAtCoord i ℬ) :
    boxFamily (Down.compression i 𝒜) (Down.compression i ℬ) = boxFamily 𝒜 ℬ := by
  rw [downCompressFamily_eq_self_of_isDownAt i h𝒜,
      downCompressFamily_eq_self_of_isDownAt i hℬ]
















def reimerStepCexA : Finset (Finset (Fin 2)) := {∅, {1}}


def reimerStepCexB : Finset (Finset (Fin 2)) := {∅, {0, 1}}


lemma reimerStep_card_box : (boxFamily reimerStepCexA reimerStepCexB).card = 3 := by
  decide



lemma reimerStep_card_box_compressed :
    (boxFamily (Down.compression 0 reimerStepCexA)
      (Down.compression 0 reimerStepCexB)).card = 2 := by
  decide









theorem reimerStep_box_compression_false :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
      (boxFamily (Down.compression i 𝒜) (Down.compression i ℬ)).card
        < (boxFamily 𝒜 ℬ).card :=
  ⟨reimerStepCexA, reimerStepCexB, 0, by
    rw [reimerStep_card_box, reimerStep_card_box_compressed]; norm_num⟩



























end StatMech
