/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Code.Inequalities.ReimerButterflyStep
import Code.Inequalities.PerOrbitCardClose

open Finset

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]





def rc_dkern (S T : Finset α) : ℕ := if Disjoint S T then 1 else 0

@[simp] lemma rc_dkern_self_disjoint {S T : Finset α} (h : Disjoint S T) :
    rc_dkern S T = 1 := by simp [rc_dkern, h]

@[simp] lemma rc_dkern_not_disjoint {S T : Finset α} (h : ¬ Disjoint S T) :
    rc_dkern S T = 0 := by simp [rc_dkern, h]


lemma rc_dkern_comm (S T : Finset α) : rc_dkern S T = rc_dkern T S := by
  simp only [rc_dkern, disjoint_comm]





theorem rc_dpairsCount_eq_doubleSum (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, rc_dkern S T := by
  unfold dpairsCount rc_dkern
  rw [Finset.card_filter, Finset.sum_product]



theorem rc_dpairsCount_eq_sum_card_fst (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, (ℬ.filter (fun T => Disjoint S T)).card := by
  rw [rc_dpairsCount_eq_doubleSum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.card_filter]; rfl



theorem rc_dpairsCount_eq_sum_card_snd (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = ∑ T ∈ ℬ, (𝒜.filter (fun S => Disjoint S T)).card := by
  rw [rc_dpairsCount_eq_doubleSum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.card_filter]; rfl






theorem rc_dpairsCount_mono_fst {𝒜 𝒜' ℬ : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') :
    dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ := by
  rw [rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum]
  exact Finset.sum_le_sum_of_subset h


theorem rc_dpairsCount_mono_snd {𝒜 ℬ ℬ' : Finset (Finset α)} (h : ℬ ⊆ ℬ') :
    dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜 ℬ' := by
  rw [rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum]
  refine Finset.sum_le_sum (fun S _ => ?_)
  exact Finset.sum_le_sum_of_subset h


theorem rc_dpairsCount_mono {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)}
    (hA : 𝒜 ⊆ 𝒜') (hB : ℬ ⊆ ℬ') :
    dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ' :=
  (rc_dpairsCount_mono_fst hA).trans (rc_dpairsCount_mono_snd hB)





theorem rc_dpairsCount_union_fst {𝒜 𝒜' ℬ : Finset (Finset α)} (h : Disjoint 𝒜 𝒜') :
    dpairsCount (𝒜 ∪ 𝒜') ℬ = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ := by
  rw [rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum,
    Finset.sum_union h]



theorem rc_dpairsCount_union_snd {𝒜 ℬ ℬ' : Finset (Finset α)} (h : Disjoint ℬ ℬ') :
    dpairsCount 𝒜 (ℬ ∪ ℬ') = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ' := by
  rw [rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_union h]






theorem rc_dpairsCount_modular_fst (𝒜 𝒜' ℬ : Finset (Finset α)) :
    dpairsCount (𝒜 ∪ 𝒜') ℬ + dpairsCount (𝒜 ∩ 𝒜') ℬ
      = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ := by
  rw [rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum,
    rc_dpairsCount_eq_doubleSum]
  exact Finset.sum_union_inter




theorem rc_dpairsCount_modular_snd (𝒜 ℬ ℬ' : Finset (Finset α)) :
    dpairsCount 𝒜 (ℬ ∪ ℬ') + dpairsCount 𝒜 (ℬ ∩ ℬ')
      = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ' := by
  rw [rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum,
    rc_dpairsCount_eq_doubleSum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  exact Finset.sum_union_inter




@[simp] theorem rc_dpairsCount_empty_fst (ℬ : Finset (Finset α)) :
    dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
  rw [rc_dpairsCount_eq_doubleSum, Finset.sum_empty]


@[simp] theorem rc_dpairsCount_empty_snd (𝒜 : Finset (Finset α)) :
    dpairsCount 𝒜 (∅ : Finset (Finset α)) = 0 := by
  rw [rc_dpairsCount_eq_doubleSum]; simp



theorem rc_dpairsCount_comm (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = dpairsCount ℬ 𝒜 := by
  rw [rc_dpairsCount_eq_doubleSum, rc_dpairsCount_eq_doubleSum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
  exact rc_dkern_comm T S

end StatMech.Walls
