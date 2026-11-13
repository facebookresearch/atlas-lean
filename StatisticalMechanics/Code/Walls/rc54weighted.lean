/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































































import Code.Inequalities.ReimerButterflyClose
import Code.Walls.rc53butterfly
import Code.Walls.rc22doublecover

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]











theorem rc54_fwt_one (S : Finset α) : fwt (fun _ _ => (1 : ℝ)) S = 1 := by
  unfold fwt; simp





theorem rc54_wdpairs_one_eq_dpairsCount (𝒜 ℬ : Finset (Finset α)) :
    wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = (dpairsCount 𝒜 ℬ : ℝ) := by
  unfold wdpairs dpairsCount
  rw [Finset.card_eq_sum_ones]
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  rw [rc54_fwt_one, rc54_fwt_one]; ring





theorem rc54_wdpairs_one_eq_card_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = ((boxDoubled 𝒜 ℬ).card : ℝ) := by
  rw [rc54_wdpairs_one_eq_dpairsCount, card_boxDoubled_eq_dpairsCount]














theorem rc54_wdpairs_le_fmarg_mul {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ :=
  wdpairs_le_mul hw 𝒜 ℬ






theorem rc54_wdpairs_add_member_le_mul {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b)
    (𝒜 ℬ : Finset (Finset α)) (i : α) :
    wdpairs w 𝒜 ℬ
        + w i true * w i true * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
      ≤ fmarg w 𝒜 * fmarg w ℬ :=
  wdpairs_add_member_le_mul hw 𝒜 ℬ i




theorem rc54_wdpairs_fiber_recursion (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    wdpairs w 𝒜 ℬ
      = w i false * w i false * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
      + w i true * w i false * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
      + w i false * w i true * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) :=
  wdpairs_fiber_recursion w 𝒜 ℬ i












theorem rc54_wdpairs_one_butterfly_invariant (i : α) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ
      = ((doubleCompress i (boxDoubled 𝒜 ℬ)).card : ℝ) := by
  rw [rc54_wdpairs_one_eq_card_boxDoubled, doubleCompress_card]











open Classical in



theorem rc54_reflInter_eq_inter_complFam (𝒜 ℬ : Finset (Finset α)) :
    rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc22_complFam ℬ :=
  rc22_reflInter_eq_inter_complFam 𝒜 ℬ

open Classical in





theorem rc54_reflInter_card_le_wdpairs_one (𝒜 ℬ : Finset (Finset α)) :
    ((rc10_reflInter 𝒜 ℬ).card : ℝ) ≤ wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ := by
  rw [rc54_wdpairs_one_eq_dpairsCount]
  exact_mod_cast rc22_reflInter_le_dpairsCount 𝒜 ℬ













def rc54_wA : Finset (Finset (Fin 2)) := {∅, {0}}


def rc54_wB : Finset (Finset (Fin 2)) := {∅, {1}}


noncomputable def rc54_wWt : Fin 2 → Bool → ℝ := fun _ b => if b then (1 : ℝ) / 2 else 1


theorem rc54_wWt_nonneg : ∀ x b, 0 ≤ rc54_wWt x b := by
  intro x b; unfold rc54_wWt; cases b <;> norm_num



theorem rc54_famCylBox_witness :
    rc20_famCylBox rc54_wA rc54_wB = ({∅} : Finset (Finset (Fin 2))) := by
  rw [← rc20_famCylBoxComp_eq, rc54_wA, rc54_wB]; decide



theorem rc54_reflInter_witness :
    rc10_reflInter rc54_wA rc54_wB = ({{0}} : Finset (Finset (Fin 2))) := by
  rw [← rc20_reflInterComp_eq, rc54_wA, rc54_wB]; decide



theorem rc54_fmarg_famCylBox_witness :
    fmarg rc54_wWt (rc20_famCylBox rc54_wA rc54_wB) = 1 := by
  rw [rc54_famCylBox_witness]
  unfold fmarg fwt rc54_wWt
  simp [Finset.sum_singleton]



theorem rc54_fmarg_reflInter_witness :
    fmarg rc54_wWt (rc10_reflInter rc54_wA rc54_wB) = 1 / 2 := by
  rw [rc54_reflInter_witness]
  unfold fmarg fwt rc54_wWt
  rw [Finset.sum_singleton, Fin.prod_univ_two]
  norm_num





theorem rc54_witness_card_wall :
    (rc20_famCylBox rc54_wA rc54_wB).card ≤ (rc10_reflInter rc54_wA rc54_wB).card := by
  rw [rc54_famCylBox_witness, rc54_reflInter_witness]
  simp












theorem rc54_product_weighted_wall_false :
    ¬ (fmarg rc54_wWt (rc20_famCylBox rc54_wA rc54_wB)
        ≤ fmarg rc54_wWt (rc10_reflInter rc54_wA rc54_wB)) := by
  rw [rc54_fmarg_famCylBox_witness, rc54_fmarg_reflInter_witness]
  norm_num





theorem rc54_exists_product_weight_refuting_wall :
    ∃ (w : Fin 2 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 2))),
      (∀ x b, 0 ≤ w x b)
      ∧ (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card
      ∧ ¬ (fmarg w (rc20_famCylBox 𝒜 ℬ) ≤ fmarg w (rc10_reflInter 𝒜 ℬ)) :=
  ⟨rc54_wWt, rc54_wA, rc54_wB, rc54_wWt_nonneg, rc54_witness_card_wall,
    rc54_product_weighted_wall_false⟩









open Classical in



theorem rc54_reimer_of_hallDoubled (h : rc37_HallDoubled) : rc18_CylBoxReflInter :=
  rc37_reimer_closes_of_hallDoubled h

open Classical in


theorem rc54_famCylBoxResidue_of_hallDoubled (h : rc37_HallDoubled) : rc20_FamCylBoxResidue :=
  rc37_famCylBoxResidue_of_hallDoubled h

open Classical in




theorem rc54_reimerWprobCore_of_famCylBoxResidue (h : rc20_FamCylBoxResidue) : ReimerWprobCore :=
  rc18_reimerWprobCore_of_cylBoxReflInter (rc20_cylBoxReflInter_of_famCylBoxResidue h)



open Classical in






































theorem rc54_reimer_weighted_functional :
    (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
        wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = (dpairsCount 𝒜 ℬ : ℝ))
      ∧ (∀ (i : Fin 3) (𝒜 ℬ : Finset (Finset (Fin 3))),
          wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ = ((doubleCompress i (boxDoubled 𝒜 ℬ)).card : ℝ))
      ∧ (∀ (𝒜 ℬ : Finset (Finset (Fin 3))),
          ((rc10_reflInter 𝒜 ℬ).card : ℝ) ≤ wdpairs (fun _ _ => (1 : ℝ)) 𝒜 ℬ)
      ∧ (∃ (w : Fin 2 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 2))),
          (∀ x b, 0 ≤ w x b)
          ∧ (rc20_famCylBox 𝒜 ℬ).card ≤ (rc10_reflInter 𝒜 ℬ).card
          ∧ ¬ (fmarg w (rc20_famCylBox 𝒜 ℬ) ≤ fmarg w (rc10_reflInter 𝒜 ℬ)))
      ∧ (rc37_HallDoubled → rc18_CylBoxReflInter)
      ∧ (rc20_FamCylBoxResidue → ReimerWprobCore) :=
  ⟨fun 𝒜 ℬ => rc54_wdpairs_one_eq_dpairsCount 𝒜 ℬ,
    fun i 𝒜 ℬ => rc54_wdpairs_one_butterfly_invariant i 𝒜 ℬ,
    fun 𝒜 ℬ => rc54_reflInter_card_le_wdpairs_one 𝒜 ℬ,
    rc54_exists_product_weight_refuting_wall,
    rc54_reimer_of_hallDoubled,
    rc54_reimerWprobCore_of_famCylBoxResidue⟩

end StatMech.Walls
