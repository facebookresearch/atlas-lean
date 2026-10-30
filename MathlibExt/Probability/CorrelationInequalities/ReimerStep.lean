/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.ReimerCompression
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-!
# Disjoint-union families and down-compression

For families of finsets `𝒜, ℬ`, the family `𝒜 ○ ℬ` (`Finset.disjSups`) of unions `S ∪ T` with
`S ∈ 𝒜`, `T ∈ ℬ` disjoint is the set-family form of disjoint occurrence. This file records how it
interacts with Mathlib's down-compression `Down.compression`.

## Main definitions

* `StatMech.IsDownAtCoord i 𝒜`: `𝒜` is closed under erasing `i`.

## Main results

* `StatMech.downCompressFamily_eq_self_of_isDownAt`: down-compression at `i` fixes a family that
  is closed under erasing `i`.
* `StatMech.reimerStep_box_compression_false`: simultaneous down-compression of both families
  can strictly decrease `#(𝒜 ○ ℬ)`, so it cannot be used directly as a monotone step towards
  Reimer's inequality.
-/

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [DecidableEq α]

/-- The members of `𝒜 ○ ℬ` avoiding `i` are exactly the disjoint unions of members of `𝒜` and
`ℬ` avoiding `i`. -/
theorem boxFamily_filter_notMem_coord (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (𝒜 ○ ℬ).filter (fun U => i ∉ U)
      = (𝒜.filter (fun S => i ∉ S)) ○ (ℬ.filter (fun T => i ∉ T)) := by
  ext U
  simp only [mem_filter, mem_disjSups, sup_eq_union]
  constructor
  · rintro ⟨⟨S, hS, T, hT, hd, rfl⟩, hiU⟩
    rw [mem_union, not_or] at hiU
    exact ⟨S, ⟨hS, hiU.1⟩, T, ⟨hT, hiU.2⟩, hd, rfl⟩
  · rintro ⟨S, ⟨hS, hiS⟩, T, ⟨hT, hiT⟩, hd, rfl⟩
    refine ⟨⟨S, hS, T, hT, hd, rfl⟩, ?_⟩
    rw [mem_union, not_or]; exact ⟨hiS, hiT⟩

/-- `IsDownAtCoord i 𝒜`: the family `𝒜` is closed under erasing `i`. -/
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
    Down.compression i 𝒜 ○ Down.compression i ℬ = 𝒜 ○ ℬ := by
  rw [downCompressFamily_eq_self_of_isDownAt i h𝒜,
      downCompressFamily_eq_self_of_isDownAt i hℬ]

/-- The family `{∅, {1}}` on `Fin 2`, the first family of the counterexample
`StatMech.reimerStep_box_compression_false`. -/
def reimerStepCexA : Finset (Finset (Fin 2)) := {∅, {1}}

/-- The family `{∅, {0, 1}}` on `Fin 2`, the second family of the counterexample
`StatMech.reimerStep_box_compression_false`. -/
def reimerStepCexB : Finset (Finset (Fin 2)) := {∅, {0, 1}}

lemma reimerStep_card_box : (reimerStepCexA ○ reimerStepCexB).card = 3 := by
  decide

lemma reimerStep_card_box_compressed :
    (Down.compression 0 reimerStepCexA ○ Down.compression 0 reimerStepCexB).card = 2 := by
  decide

/-- Down-compressing both families at the same coordinate can strictly decrease the size of
`𝒜 ○ ℬ`. -/
theorem reimerStep_box_compression_false :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
      (Down.compression i 𝒜 ○ Down.compression i ℬ).card < (𝒜 ○ ℬ).card :=
  ⟨reimerStepCexA, reimerStepCexB, 0, by
    rw [reimerStep_card_box, reimerStep_card_box_compressed]; norm_num⟩

end StatMech
