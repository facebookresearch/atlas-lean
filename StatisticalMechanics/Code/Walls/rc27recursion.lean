/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Code.Walls.rc26cubefill

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]














def rc27_ReflInterRecursion : Prop :=
  ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E →
    #(rc14_reflE E 𝒜 ℬ)
      = #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))

open Classical in




theorem rc27_reflInterRecursion : rc27_ReflInterRecursion (α := α) :=
  fun E 𝒜 ℬ a haE => rc15_card_reflE_slice E 𝒜 ℬ a haE

open Classical in






theorem rc27_reflInter_univ_slice (𝒜 ℬ : Finset (Finset α)) (a : α) :
    #(rc10_reflInter 𝒜 ℬ)
      = #(rc14_reflE (univ.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc14_reflE (univ.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
  rw [← rc15_reflE_univ]
  exact rc15_card_reflE_slice univ 𝒜 ℬ a (Finset.mem_univ a)


























set_option maxRecDepth 10000 in






theorem rc27_boxSlice_sum_false :
    ¬ (#(rc14_boxE (univ : Finset (Fin 1)) ({∅}) ({∅}))
        ≤ #(rc14_boxE ((univ : Finset (Fin 1)).erase 0)
              (({∅} : Finset (Finset (Fin 1))).nonMemberSubfamily 0)
              (({∅} : Finset (Finset (Fin 1))).memberSubfamily 0))
          + #(rc14_boxE ((univ : Finset (Fin 1)).erase 0)
              (({∅} : Finset (Finset (Fin 1))).memberSubfamily 0)
              (({∅} : Finset (Finset (Fin 1))).nonMemberSubfamily 0))) := by
  decide

set_option maxRecDepth 10000 in







theorem rc27_boxNesting_false :
    ¬ (rc14_boxE ((univ : Finset (Fin 2)).erase 1)
          (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1)
          (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1)
        ⊆ rc14_boxE ((univ : Finset (Fin 2)).erase 1)
              (({∅} : Finset (Finset (Fin 2))).memberSubfamily 1)
              (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1)
            ∩ rc14_boxE ((univ : Finset (Fin 2)).erase 1)
              (({∅} : Finset (Finset (Fin 2))).nonMemberSubfamily 1)
              (({∅} : Finset (Finset (Fin 2))).memberSubfamily 1)) := by
  decide
























def rc27_BoxSuppRecursion : Prop :=
  ∀ (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α), a ∈ E →
    #(rc14_boxE E 𝒜 ℬ)
      ≤ #(rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))
        + #(rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))

open Classical in



theorem rc27_boxE_le_reflE_empty (𝒜 ℬ : Finset (Finset α)) :
    #(rc14_boxE (∅ : Finset α) 𝒜 ℬ) ≤ #(rc14_reflE (∅ : Finset α) 𝒜 ℬ) := by
  apply Finset.card_le_card
  intro S hS
  rw [rc14_mem_boxE] at hS
  obtain ⟨hSE, K, L, _, hKS, hLS, hK, hL⟩ := hS
  have hS0 : S = ∅ := Finset.subset_empty.mp hSE
  subst hS0
  have hK0 : K = ∅ := Finset.subset_empty.mp hKS
  have hL0 : L = ∅ := Finset.subset_empty.mp hLS
  subst hK0; subst hL0
  rw [rc14_mem_reflE]
  refine ⟨Finset.Subset.refl _, hK, ?_⟩
  simpa using hL

open Classical in










theorem rc27_boxE_le_reflE_of_boxRecursion (h : rc27_BoxSuppRecursion (α := α)) :
    ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α),
      #(rc14_boxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ) := by
  intro E
  induction E using Finset.strongInduction with
  | _ E ih =>
    intro 𝒜 ℬ
    rcases E.eq_empty_or_nonempty with rfl | ⟨a, haE⟩
    · exact rc27_boxE_le_reflE_empty 𝒜 ℬ
    · have hIHmn : #(rc14_boxE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a))
          ≤ #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) :=
        ih (E.erase a) (Finset.erase_ssubset haE) _ _
      have hIHnm : #(rc14_boxE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
          ≤ #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)) :=
        ih (E.erase a) (Finset.erase_ssubset haE) _ _
      have hbox := h E 𝒜 ℬ a haE
      have hrefl := rc27_reflInterRecursion E 𝒜 ℬ a haE
      omega








theorem rc27_boxSupp_le_reflInter_of_boxRecursion (h : rc27_BoxSuppRecursion (α := α))
    (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  have := rc27_boxE_le_reflE_of_boxRecursion h univ 𝒜 ℬ
  rwa [rc15_boxE_univ, rc15_reflE_univ] at this

set_option maxRecDepth 10000 in






theorem rc27_boxSuppRecursion_false : ¬ rc27_BoxSuppRecursion (α := Fin 1) := by
  intro h
  exact rc27_boxSlice_sum_false (h univ ({∅}) ({∅}) 0 (Finset.mem_univ 0))








set_option maxRecDepth 10000 in






theorem rc27_reflInter_recursion_witness :
    #(rc10_reflInter ({∅, {0}, {2}, {0, 2}} : Finset (Finset (Fin 3)))
        ({{1}, {2}, {1, 2}, {0, 1, 2}})) = 2 + 1
      ∧ #(rc14_reflE ((univ : Finset (Fin 3)).erase 2)
            (({∅, {0}, {2}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 2)
            (({{1}, {2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 2)) = 2
      ∧ #(rc14_reflE ((univ : Finset (Fin 3)).erase 2)
            (({∅, {0}, {2}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 2)
            (({{1}, {2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 2)) = 1 := by
  have h1 : #(rc14_reflE ((univ : Finset (Fin 3)).erase 2)
            (({∅, {0}, {2}, {0, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 2)
            (({{1}, {2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))).memberSubfamily 2)) = 2 := by
    decide
  have h2 : #(rc14_reflE ((univ : Finset (Fin 3)).erase 2)
            (({∅, {0}, {2}, {0, 2}} : Finset (Finset (Fin 3))).memberSubfamily 2)
            (({{1}, {2}, {1, 2}, {0, 1, 2}} : Finset (Finset (Fin 3))).nonMemberSubfamily 2)) = 1 := by
    decide
  refine ⟨?_, h1, h2⟩
  rw [rc27_reflInter_univ_slice ({∅, {0}, {2}, {0, 2}}) ({{1}, {2}, {1, 2}, {0, 1, 2}}) 2, h1, h2]



open Classical in






















theorem rc27_reimer_recursion :
    rc27_ReflInterRecursion (α := α)
      ∧ (∀ (𝒜 ℬ : Finset (Finset α)) (a : α),
          #(rc10_reflInter 𝒜 ℬ)
            = #(rc14_reflE (univ.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
              + #(rc14_reflE (univ.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)))
      ∧ (¬ rc27_BoxSuppRecursion (α := Fin 1))
      ∧ (rc27_BoxSuppRecursion (α := α) →
          ∀ E : Finset α, ∀ 𝒜 ℬ : Finset (Finset α),
            #(rc14_boxE E 𝒜 ℬ) ≤ #(rc14_reflE E 𝒜 ℬ)) :=
  ⟨rc27_reflInterRecursion,
    rc27_reflInter_univ_slice,
    rc27_boxSuppRecursion_false,
    rc27_boxE_le_reflE_of_boxRecursion⟩

end StatMech.Walls
