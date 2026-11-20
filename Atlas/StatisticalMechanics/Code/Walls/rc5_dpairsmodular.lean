/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Code.Inequalities.ReimerButterflyStep
import Code.Walls.rc_dpairsfiberrecursion
import Mathlib.Combinatorics.SetFamily.Compression.Down

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]





def rc5_dkern (S T : Finset α) : ℕ := if Disjoint S T then 1 else 0

@[simp] lemma rc5_dkern_self_disjoint {S T : Finset α} (h : Disjoint S T) :
    rc5_dkern S T = 1 := by simp [rc5_dkern, h]

@[simp] lemma rc5_dkern_not_disjoint {S T : Finset α} (h : ¬ Disjoint S T) :
    rc5_dkern S T = 0 := by simp [rc5_dkern, h]


lemma rc5_dkern_comm (S T : Finset α) : rc5_dkern S T = rc5_dkern T S := by
  simp only [rc5_dkern, disjoint_comm]





theorem rc5_dpairsCount_eq_doubleSum (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, rc5_dkern S T := by
  unfold dpairsCount rc5_dkern
  rw [Finset.card_filter, Finset.sum_product]



theorem rc5_dpairsCount_eq_sum_card_fst (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, (ℬ.filter (fun T => Disjoint S T)).card := by
  rw [rc5_dpairsCount_eq_doubleSum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.card_filter]; rfl



theorem rc5_dpairsCount_eq_sum_card_snd (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = ∑ T ∈ ℬ, (𝒜.filter (fun S => Disjoint S T)).card := by
  rw [rc5_dpairsCount_eq_doubleSum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [Finset.card_filter]; rfl






theorem rc5_dpairsCount_mono_fst {𝒜 𝒜' ℬ : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') :
    dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ := by
  rw [rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum]
  exact Finset.sum_le_sum_of_subset h


theorem rc5_dpairsCount_mono_snd {𝒜 ℬ ℬ' : Finset (Finset α)} (h : ℬ ⊆ ℬ') :
    dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜 ℬ' := by
  rw [rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum]
  refine Finset.sum_le_sum (fun S _ => ?_)
  exact Finset.sum_le_sum_of_subset h


theorem rc5_dpairsCount_mono {𝒜 𝒜' ℬ ℬ' : Finset (Finset α)}
    (hA : 𝒜 ⊆ 𝒜') (hB : ℬ ⊆ ℬ') :
    dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ' :=
  (rc5_dpairsCount_mono_fst hA).trans (rc5_dpairsCount_mono_snd hB)





theorem rc5_dpairsCount_union_fst {𝒜 𝒜' ℬ : Finset (Finset α)} (h : Disjoint 𝒜 𝒜') :
    dpairsCount (𝒜 ∪ 𝒜') ℬ = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ := by
  rw [rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum,
    Finset.sum_union h]



theorem rc5_dpairsCount_union_snd {𝒜 ℬ ℬ' : Finset (Finset α)} (h : Disjoint ℬ ℬ') :
    dpairsCount 𝒜 (ℬ ∪ ℬ') = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ' := by
  rw [rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_union h]






theorem rc5_dpairsCount_modular_fst (𝒜 𝒜' ℬ : Finset (Finset α)) :
    dpairsCount (𝒜 ∪ 𝒜') ℬ + dpairsCount (𝒜 ∩ 𝒜') ℬ
      = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ := by
  rw [rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum,
    rc5_dpairsCount_eq_doubleSum]
  exact Finset.sum_union_inter




theorem rc5_dpairsCount_modular_snd (𝒜 ℬ ℬ' : Finset (Finset α)) :
    dpairsCount 𝒜 (ℬ ∪ ℬ') + dpairsCount 𝒜 (ℬ ∩ ℬ')
      = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ' := by
  rw [rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum,
    rc5_dpairsCount_eq_doubleSum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  exact Finset.sum_union_inter




@[simp] theorem rc5_dpairsCount_empty_fst (ℬ : Finset (Finset α)) :
    dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
  rw [rc5_dpairsCount_eq_doubleSum, Finset.sum_empty]


@[simp] theorem rc5_dpairsCount_empty_snd (𝒜 : Finset (Finset α)) :
    dpairsCount 𝒜 (∅ : Finset (Finset α)) = 0 := by
  rw [rc5_dpairsCount_eq_doubleSum]; simp



theorem rc5_dpairsCount_comm (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = dpairsCount ℬ 𝒜 := by
  rw [rc5_dpairsCount_eq_doubleSum, rc5_dpairsCount_eq_doubleSum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
  exact rc5_dkern_comm T S

























theorem rc5_downComp_nonMemberSubfamily (i : α) (𝒜 : Finset (Finset α)) :
    (Down.compression i 𝒜).nonMemberSubfamily i
      = 𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i := by
  ext s
  simp only [mem_nonMemberSubfamily, mem_union, mem_memberSubfamily, Down.mem_compression]
  constructor
  · rintro ⟨h, hns⟩
    rcases h with ⟨hin, _⟩ | ⟨_, hins⟩
    · exact Or.inr ⟨hin, hns⟩
    · exact Or.inl ⟨hins, hns⟩
  · rintro (⟨hins, hns⟩ | ⟨hin, hns⟩)
    · refine ⟨?_, hns⟩
      by_cases hsA : s ∈ 𝒜
      · exact Or.inl ⟨hsA, by rw [erase_eq_of_notMem hns]; exact hsA⟩
      · exact Or.inr ⟨hsA, hins⟩
    · exact ⟨Or.inl ⟨hin, by rw [erase_eq_of_notMem hns]; exact hin⟩, hns⟩




theorem rc5_downComp_memberSubfamily (i : α) (𝒜 : Finset (Finset α)) :
    (Down.compression i 𝒜).memberSubfamily i
      = 𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i := by
  ext s
  simp only [mem_memberSubfamily, mem_inter, mem_nonMemberSubfamily, Down.mem_compression]
  constructor
  · rintro ⟨h, hns⟩
    rcases h with ⟨hin, herase⟩ | ⟨hnin, hins⟩
    · rw [erase_insert hns] at herase; exact ⟨⟨hin, hns⟩, herase, hns⟩
    · rw [insert_idem] at hins; exact absurd hins hnin
  · rintro ⟨⟨hin, hns⟩, hsA, _⟩
    exact ⟨Or.inl ⟨hin, by rw [erase_insert hns]; exact hsA⟩, hns⟩










theorem rc5_fiber_downDown_ineq (am an bm bn : Finset (Finset α)) :
    dpairsCount an bn + dpairsCount am bn + dpairsCount an bm
      ≤ dpairsCount (am ∪ an) (bm ∪ bn) + dpairsCount (am ∩ an) (bm ∪ bn)
        + dpairsCount (am ∪ an) (bm ∩ bn) := by
  have e1 := rc5_dpairsCount_modular_fst am an (bm ∪ bn)
  have e2 := rc5_dpairsCount_modular_fst am an (bm ∩ bn)
  have e3 := rc5_dpairsCount_modular_snd am bm bn
  have e4 := rc5_dpairsCount_modular_snd an bm bn
  have e5 := rc5_dpairsCount_modular_snd (am ∩ an) bm bn
  have hmono : dpairsCount (am ∩ an) (bm ∩ bn) ≤ dpairsCount am bm :=
    rc5_dpairsCount_mono Finset.inter_subset_left Finset.inter_subset_left
  omega













theorem rc5_dpairsCount_downDown_mono (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
  rw [rc_dpairsCount_fiber_recursion 𝒜 ℬ i,
    rc_dpairsCount_fiber_recursion (Down.compression i 𝒜) (Down.compression i ℬ) i,
    rc5_downComp_nonMemberSubfamily i 𝒜, rc5_downComp_memberSubfamily i 𝒜,
    rc5_downComp_nonMemberSubfamily i ℬ, rc5_downComp_memberSubfamily i ℬ]
  exact rc5_fiber_downDown_ineq _ _ _ _








theorem rc5_deficit_identity (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ
      = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
        - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
            (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
  rw [rc_dpairsCount_fiber_recursion 𝒜 ℬ i,
    rc_dpairsCount_fiber_recursion (Down.compression i 𝒜) (Down.compression i ℬ) i,
    rc5_downComp_nonMemberSubfamily i 𝒜, rc5_downComp_memberSubfamily i 𝒜,
    rc5_downComp_nonMemberSubfamily i ℬ, rc5_downComp_memberSubfamily i ℬ]
  set am := 𝒜.memberSubfamily i
  set an := 𝒜.nonMemberSubfamily i
  set bm := ℬ.memberSubfamily i
  set bn := ℬ.nonMemberSubfamily i
  have e1 := rc5_dpairsCount_modular_fst am an (bm ∪ bn)
  have e2 := rc5_dpairsCount_modular_fst am an (bm ∩ bn)
  have e3 := rc5_dpairsCount_modular_snd am bm bn
  have e4 := rc5_dpairsCount_modular_snd an bm bn
  have e5 := rc5_dpairsCount_modular_snd (am ∩ an) bm bn
  push_cast
  omega



theorem rc5_deficit_nonneg (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (0 : ℤ) ≤ (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
        - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
            (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
  rw [← rc5_deficit_identity 𝒜 ℬ i, sub_nonneg]
  exact_mod_cast rc5_dpairsCount_downDown_mono 𝒜 ℬ i








theorem rc5_card_boxDoubled_downDown_mono (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (boxDoubled 𝒜 ℬ).card
      ≤ (boxDoubled (Down.compression i 𝒜) (Down.compression i ℬ)).card := by
  rw [card_boxDoubled_eq_dpairsCount, card_boxDoubled_eq_dpairsCount]
  exact rc5_dpairsCount_downDown_mono 𝒜 ℬ i


















theorem rc5_dpairsmodular (𝒜 𝒜' ℬ ℬ' : Finset (Finset α)) (i : α) :
    (dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, rc5_dkern S T)
      ∧ (𝒜 ⊆ 𝒜' → ℬ ⊆ ℬ' → dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ')
      ∧ (dpairsCount (𝒜 ∪ 𝒜') ℬ + dpairsCount (𝒜 ∩ 𝒜') ℬ
          = dpairsCount 𝒜 ℬ + dpairsCount 𝒜' ℬ)
      ∧ (dpairsCount 𝒜 (ℬ ∪ ℬ') + dpairsCount 𝒜 (ℬ ∩ ℬ')
          = dpairsCount 𝒜 ℬ + dpairsCount 𝒜 ℬ')
      ∧ (dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) :=
  ⟨rc5_dpairsCount_eq_doubleSum 𝒜 ℬ,
    fun hA hB => rc5_dpairsCount_mono hA hB,
    rc5_dpairsCount_modular_fst 𝒜 𝒜' ℬ,
    rc5_dpairsCount_modular_snd 𝒜 ℬ ℬ',
    rc5_dpairsCount_downDown_mono 𝒜 ℬ i⟩

end StatMech.Walls
