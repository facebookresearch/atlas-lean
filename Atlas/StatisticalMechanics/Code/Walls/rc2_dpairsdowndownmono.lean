/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Code.Walls.rc_doubledboxcount
import Code.Walls.rc_dpairsfiberrecursion
import Code.Walls.rc_dpairsmodular
import Mathlib.Combinatorics.SetFamily.Compression.Down

open Finset
open scoped FinsetFamily

namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]













theorem rc2_downComp_nonMemberSubfamily (i : α) (𝒜 : Finset (Finset α)) :
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




theorem rc2_downComp_memberSubfamily (i : α) (𝒜 : Finset (Finset α)) :
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




















theorem rc2_fiber_downDown_ineq (am an bm bn : Finset (Finset α)) :
    dpairsCount an bn + dpairsCount am bn + dpairsCount an bm
      ≤ dpairsCount (am ∪ an) (bm ∪ bn) + dpairsCount (am ∩ an) (bm ∪ bn)
        + dpairsCount (am ∪ an) (bm ∩ bn) := by
  have e1 := rc_dpairsCount_modular_fst am an (bm ∪ bn)
  have e2 := rc_dpairsCount_modular_fst am an (bm ∩ bn)
  have e3 := rc_dpairsCount_modular_snd am bm bn
  have e4 := rc_dpairsCount_modular_snd an bm bn
  have e5 := rc_dpairsCount_modular_snd (am ∩ an) bm bn
  have hmono : dpairsCount (am ∩ an) (bm ∩ bn) ≤ dpairsCount am bm :=
    rc_dpairsCount_mono Finset.inter_subset_left Finset.inter_subset_left
  omega






















theorem rc2_dpairsCount_downDown_mono (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
  rw [rc_dpairsCount_fiber_recursion 𝒜 ℬ i,
    rc_dpairsCount_fiber_recursion (Down.compression i 𝒜) (Down.compression i ℬ) i,
    rc2_downComp_nonMemberSubfamily i 𝒜, rc2_downComp_memberSubfamily i 𝒜,
    rc2_downComp_nonMemberSubfamily i ℬ, rc2_downComp_memberSubfamily i ℬ]
  exact rc2_fiber_downDown_ineq _ _ _ _














theorem rc2_deficit_identity (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ
      = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
        - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
            (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
  rw [rc_dpairsCount_fiber_recursion 𝒜 ℬ i,
    rc_dpairsCount_fiber_recursion (Down.compression i 𝒜) (Down.compression i ℬ) i,
    rc2_downComp_nonMemberSubfamily i 𝒜, rc2_downComp_memberSubfamily i 𝒜,
    rc2_downComp_nonMemberSubfamily i ℬ, rc2_downComp_memberSubfamily i ℬ]
  set am := 𝒜.memberSubfamily i
  set an := 𝒜.nonMemberSubfamily i
  set bm := ℬ.memberSubfamily i
  set bn := ℬ.nonMemberSubfamily i
  have e1 := rc_dpairsCount_modular_fst am an (bm ∪ bn)
  have e2 := rc_dpairsCount_modular_fst am an (bm ∩ bn)
  have e3 := rc_dpairsCount_modular_snd am bm bn
  have e4 := rc_dpairsCount_modular_snd an bm bn
  have e5 := rc_dpairsCount_modular_snd (am ∩ an) bm bn
  push_cast
  omega



theorem rc2_deficit_nonneg (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (0 : ℤ) ≤ (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ)
        - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i)
            (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
  rw [← rc2_deficit_identity 𝒜 ℬ i, sub_nonneg]
  exact_mod_cast rc2_dpairsCount_downDown_mono 𝒜 ℬ i












theorem rc2_card_boxDoubled_downDown_mono (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (boxDoubled 𝒜 ℬ).card
      ≤ (boxDoubled (Down.compression i 𝒜) (Down.compression i ℬ)).card := by
  rw [rc_card_boxDoubled_eq_dpairsViaInjOn, rc_card_boxDoubled_eq_dpairsViaInjOn]
  exact rc2_dpairsCount_downDown_mono 𝒜 ℬ i

end StatMech.Walls
