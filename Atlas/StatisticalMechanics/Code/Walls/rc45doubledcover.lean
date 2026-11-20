/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Code.Walls.rc44boxineq
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]







omit [Fintype α] in


theorem rc45_slab1_card (a : α) (𝒜 : Finset (Finset α)) :
    (rc44_slab1 a 𝒜).card = (𝒜.filter (fun S => a ∈ S)).card := by
  rw [rc44_slab1]
  refine Finset.card_image_of_injOn ?_
  intro S hS S' hS' h
  simp only at h
  rw [Finset.mem_coe, Finset.mem_filter] at hS hS'
  rw [← Finset.insert_erase hS.2, ← Finset.insert_erase hS'.2, h]

omit [Fintype α] in


theorem rc45_slab_card_partition (a : α) (𝒜 : Finset (Finset α)) :
    𝒜.card = (rc44_slab0 a 𝒜).card + (rc44_slab1 a 𝒜).card := by
  rw [rc45_slab1_card, rc44_slab0]
  rw [add_comm]
  exact (Finset.card_filter_add_card_filter_not (fun S => a ∈ S)).symm










open Classical in









theorem rc45_famCylBoxE_card_diagonal_ub (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (rc44_famCylBoxE E 𝒜 ℬ).card
      ≤ (rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ)).card
        + (rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ)).card := by
  rw [rc45_slab_card_partition a (rc44_famCylBoxE E 𝒜 ℬ)]
  exact Nat.add_le_add
    (Finset.card_le_card (rc44_slab0_famCylBoxE_subset E a 𝒜 ℬ))
    (Finset.card_le_card (rc44_slab1_famCylBoxE_subset E a 𝒜 ℬ))







open Classical in







theorem rc45_reflInterE_card_antidiagonal (E : Finset α) (a : α) (haE : a ∈ E)
    (𝒜 ℬ : Finset (Finset α)) :
    (rc44_reflInterE E 𝒜 ℬ).card
      = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card
        + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card :=
  rc44_reflInterE_card_recursion E a haE 𝒜 ℬ








def rc45_Astep : Finset (Finset (Fin 3)) := {{0}, {0, 2}, {1, 2}}


def rc45_Bstep : Finset (Finset (Fin 3)) := {{0, 1, 2}, {0, 2}, {1, 2}, {2}}










theorem rc45_diagonalBox_exceeds_reflInter_fin3 :
    (rc44_reflInterEComp (Finset.univ : Finset (Fin 3)) rc45_Astep rc45_Bstep).card
      < (rc44_famCylBoxEComp {0, 1}
            (rc44_slab0 2 rc45_Astep) (rc44_slab0 2 rc45_Bstep)).card
        + (rc44_famCylBoxEComp {0, 1}
            (rc44_slab1 2 rc45_Astep) (rc44_slab1 2 rc45_Bstep)).card := by
  rw [rc45_Astep, rc45_Bstep, rc44_slab0, rc44_slab0, rc44_slab1, rc44_slab1]
  decide


def rc45_Aswap : Finset (Finset (Fin 3)) := {{0}, {0, 1}, {0, 1, 2}}


def rc45_Bswap : Finset (Finset (Fin 3)) := {{1}}










theorem rc45_reflInterE_slabSwap_fails_fin3 :
    (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card
        + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card
      < (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card
        + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card := by
  rw [rc45_Aswap, rc45_Bswap, rc44_slab0, rc44_slab0, rc44_slab1, rc44_slab1]
  decide








open Classical in


theorem rc45_reimer_closes_of_boxMonoResidue (h : rc44_BoxMonoResidue) :
    rc18_CylBoxReflInter :=
  rc44_reimer_closes_of_boxMonoResidue h

open Classical in


theorem rc45_boxMonoResidue_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) :=
  rc44_boxMonoResidue_fin2 𝒜 ℬ



set_option linter.unusedVariables false in
open Classical in


































theorem rc45_reimer_doubledcover :
    (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)),
        (rc44_famCylBoxE E 𝒜 ℬ).card
          ≤ (rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ)).card
            + (rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ)).card)
      ∧ (∀ (E : Finset α) (a : α), a ∈ E → ∀ (𝒜 ℬ : Finset (Finset α)),
          (rc44_reflInterE E 𝒜 ℬ).card
            = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card
              + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card)
      ∧ ((rc44_reflInterEComp (Finset.univ : Finset (Fin 3)) rc45_Astep rc45_Bstep).card
            < (rc44_famCylBoxEComp {0, 1}
                  (rc44_slab0 2 rc45_Astep) (rc44_slab0 2 rc45_Bstep)).card
              + (rc44_famCylBoxEComp {0, 1}
                  (rc44_slab1 2 rc45_Astep) (rc44_slab1 2 rc45_Bstep)).card)
      ∧ ((rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card
            + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card
          < (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card
            + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card)
      ∧ (rc44_BoxMonoResidue → rc18_CylBoxReflInter) :=
  ⟨fun E a 𝒜 ℬ => rc45_famCylBoxE_card_diagonal_ub E a 𝒜 ℬ,
    fun E a haE 𝒜 ℬ => rc45_reflInterE_card_antidiagonal E a haE 𝒜 ℬ,
    rc45_diagonalBox_exceeds_reflInter_fin3,
    rc45_reflInterE_slabSwap_fails_fin3,
    rc45_reimer_closes_of_boxMonoResidue⟩

end StatMech.Walls
