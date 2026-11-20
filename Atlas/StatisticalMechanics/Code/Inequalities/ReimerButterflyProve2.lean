/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Code.Inequalities.ReimerButterflyClose
import Code.Inequalities.ReimerButterflyProve
import Mathlib.Combinatorics.SetFamily.Compression.Down

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [DecidableEq α]












theorem downComp_nonMemberSubfamily (i : α) (𝒜 : Finset (Finset α)) :
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




theorem downComp_memberSubfamily (i : α) (𝒜 : Finset (Finset α)) :
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








theorem dpairsCount_double_sum (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, (if Disjoint S T then 1 else 0) := by
  unfold dpairsCount
  rw [Finset.card_filter, Finset.sum_product]


theorem dpairsCount_mono_left {𝒜 𝒜' : Finset (Finset α)} (ℬ : Finset (Finset α))
    (h : 𝒜 ⊆ 𝒜') : dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ := by
  rw [dpairsCount_double_sum, dpairsCount_double_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro S _ _; exact Finset.sum_nonneg (fun T _ => by split <;> simp)


theorem dpairsCount_mono_right (𝒞 : Finset (Finset α)) {ℬ ℬ' : Finset (Finset α)}
    (h : ℬ ⊆ ℬ') : dpairsCount 𝒞 ℬ ≤ dpairsCount 𝒞 ℬ' := by
  rw [dpairsCount_double_sum, dpairsCount_double_sum]
  apply Finset.sum_le_sum; intro S _
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro T _ _; split <;> simp



theorem dpairsCount_modular_left (𝒜 ℬ 𝒞 : Finset (Finset α)) :
    dpairsCount (𝒜 ∪ ℬ) 𝒞 + dpairsCount (𝒜 ∩ ℬ) 𝒞
      = dpairsCount 𝒜 𝒞 + dpairsCount ℬ 𝒞 := by
  simp only [dpairsCount_double_sum]; exact Finset.sum_union_inter


theorem dpairsCount_modular_right (𝒜 ℬ 𝒞 : Finset (Finset α)) :
    dpairsCount 𝒞 (𝒜 ∪ ℬ) + dpairsCount 𝒞 (𝒜 ∩ ℬ)
      = dpairsCount 𝒞 𝒜 + dpairsCount 𝒞 ℬ := by
  simp only [dpairsCount_double_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun S _ => Finset.sum_union_inter)















theorem dpairsCount_fiber_downDown_ineq (am an bm bn : Finset (Finset α)) :
    dpairsCount an bn + dpairsCount am bn + dpairsCount an bm
      ≤ dpairsCount (am ∪ an) (bm ∪ bn) + dpairsCount (am ∩ an) (bm ∪ bn)
        + dpairsCount (am ∪ an) (bm ∩ bn) := by
  have e1 := dpairsCount_modular_left am an (bm ∪ bn)
  have e2 := dpairsCount_modular_left am an (bm ∩ bn)
  have e3 := dpairsCount_modular_right bm bn am
  have e4 := dpairsCount_modular_right bm bn an
  have e5 := dpairsCount_modular_right bm bn (am ∩ an)
  have hmono : dpairsCount (am ∩ an) (bm ∩ bn) ≤ dpairsCount am bm :=
    le_trans (dpairsCount_mono_left _ Finset.inter_subset_left)
             (dpairsCount_mono_right _ Finset.inter_subset_left)
  omega

















theorem dpairsCount_downDown_mono (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
  rw [dpairsCount_fiber_recursion 𝒜 ℬ i,
    dpairsCount_fiber_recursion (Down.compression i 𝒜) (Down.compression i ℬ) i,
    downComp_nonMemberSubfamily i 𝒜, downComp_memberSubfamily i 𝒜,
    downComp_nonMemberSubfamily i ℬ, downComp_memberSubfamily i ℬ]
  exact dpairsCount_fiber_downDown_ineq _ _ _ _

section Weighted

variable [Fintype α]









noncomputable def pairKernel' (w : α → Bool → ℝ) (i : α) (S T : Finset α) : ℝ :=
  if Disjoint S T then fwt' w i S * fwt' w i T else 0


theorem wdpairs'_double_sum (w : α → Bool → ℝ) (i : α) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs' w i 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, pairKernel' w i S T := by
  unfold wdpairs' pairKernel'
  rw [Finset.sum_filter, Finset.sum_product]


theorem pairKernel'_nonneg {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α) (S T : Finset α) :
    0 ≤ pairKernel' w i S T := by
  unfold pairKernel'; split
  · exact mul_nonneg (fwt'_nonneg hw _ _) (fwt'_nonneg hw _ _)
  · rfl


theorem wdpairs'_mono_left {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    {𝒜 𝒜' : Finset (Finset α)} (ℬ : Finset (Finset α)) (h : 𝒜 ⊆ 𝒜') :
    wdpairs' w i 𝒜 ℬ ≤ wdpairs' w i 𝒜' ℬ := by
  rw [wdpairs'_double_sum, wdpairs'_double_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun S _ _ => Finset.sum_nonneg (fun T _ => pairKernel'_nonneg hw i S T))


theorem wdpairs'_mono_right {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    (𝒞 : Finset (Finset α)) {ℬ ℬ' : Finset (Finset α)} (h : ℬ ⊆ ℬ') :
    wdpairs' w i 𝒞 ℬ ≤ wdpairs' w i 𝒞 ℬ' := by
  rw [wdpairs'_double_sum, wdpairs'_double_sum]
  exact Finset.sum_le_sum (fun S _ =>
    Finset.sum_le_sum_of_subset_of_nonneg h (fun T _ _ => pairKernel'_nonneg hw i S T))


theorem wdpairs'_modular_left (w : α → Bool → ℝ) (i : α) (𝒜 ℬ 𝒞 : Finset (Finset α)) :
    wdpairs' w i (𝒜 ∪ ℬ) 𝒞 + wdpairs' w i (𝒜 ∩ ℬ) 𝒞
      = wdpairs' w i 𝒜 𝒞 + wdpairs' w i ℬ 𝒞 := by
  simp only [wdpairs'_double_sum]; exact Finset.sum_union_inter


theorem wdpairs'_modular_right (w : α → Bool → ℝ) (i : α) (𝒜 ℬ 𝒞 : Finset (Finset α)) :
    wdpairs' w i 𝒞 (𝒜 ∪ ℬ) + wdpairs' w i 𝒞 (𝒜 ∩ ℬ)
      = wdpairs' w i 𝒞 𝒜 + wdpairs' w i 𝒞 ℬ := by
  simp only [wdpairs'_double_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun S _ => Finset.sum_union_inter)




















theorem wdpairs'_fiber_downDown_ineq {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    (hdom : w i true ≤ w i false) (am an bm bn : Finset (Finset α)) :
    w i false * w i false * wdpairs' w i an bn
        + w i true * w i false * wdpairs' w i am bn
        + w i false * w i true * wdpairs' w i an bm
      ≤ w i false * w i false * wdpairs' w i (am ∪ an) (bm ∪ bn)
        + w i true * w i false * wdpairs' w i (am ∩ an) (bm ∪ bn)
        + w i false * w i true * wdpairs' w i (am ∪ an) (bm ∩ bn) := by
  have hw0 : 0 ≤ w i false := hw i false
  have hw1 : 0 ≤ w i true := hw i true
  
  have hC2 : wdpairs' w i an bn ≤ wdpairs' w i (am ∪ an) (bm ∪ bn) :=
    le_trans (wdpairs'_mono_left hw i _ Finset.subset_union_right)
             (wdpairs'_mono_right hw i _ Finset.subset_union_right)
  
  have hMono : wdpairs' w i (am ∩ an) (bm ∩ bn) ≤ wdpairs' w i am bm :=
    le_trans (wdpairs'_mono_left hw i _ Finset.inter_subset_left)
             (wdpairs'_mono_right hw i _ Finset.inter_subset_left)
  set w0 := w i false
  set w1 := w i true
  set Dcc := wdpairs' w i (am ∪ an) (bm ∪ bn)
  set DUc := wdpairs' w i (am ∩ an) (bm ∪ bn)
  set DcU := wdpairs' w i (am ∪ an) (bm ∩ bn)
  set Dapbp := wdpairs' w i am bm
  set DUX := wdpairs' w i (am ∩ an) (bm ∩ bn)
  set Danbn := wdpairs' w i an bn
  set Dambn := wdpairs' w i am bn
  set Danbm := wdpairs' w i an bm
  
  have hlin : Dcc + DUc + DcU + DUX = Dapbp + Dambn + Danbm + Danbn := by
    have ml1 : Dcc + DUc = wdpairs' w i am (bm ∪ bn) + wdpairs' w i an (bm ∪ bn) :=
      wdpairs'_modular_left w i am an (bm ∪ bn)
    have ml2 : DcU + DUX = wdpairs' w i am (bm ∩ bn) + wdpairs' w i an (bm ∩ bn) :=
      wdpairs'_modular_left w i am an (bm ∩ bn)
    have mr1 : wdpairs' w i am (bm ∪ bn) + wdpairs' w i am (bm ∩ bn) = Dapbp + Dambn :=
      wdpairs'_modular_right w i bm bn am
    have mr2 : wdpairs' w i an (bm ∪ bn) + wdpairs' w i an (bm ∩ bn) = Danbm + Danbn :=
      wdpairs'_modular_right w i bm bn an
    linarith [ml1, ml2, mr1, mr2]
  
  have key : (w0 * w0 * Dcc + w1 * w0 * DUc + w0 * w1 * DcU)
              - (w0 * w0 * Danbn + w1 * w0 * Dambn + w0 * w1 * Danbm)
           = w0 * (w0 - w1) * (Dcc - Danbn) + w0 * w1 * (Dapbp - DUX) := by
    linear_combination (w0 * w1) * hlin
  linarith [key, mul_nonneg (mul_nonneg hw0 (sub_nonneg.mpr hdom)) (sub_nonneg.mpr hC2),
    mul_nonneg (mul_nonneg hw0 hw1) (sub_nonneg.mpr hMono)]













theorem wdpairs_downDown_mono {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    (hdom : w i true ≤ w i false) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ wdpairs w (Down.compression i 𝒜) (Down.compression i ℬ) := by
  rw [wdpairs_fiber_recursion w 𝒜 ℬ i,
    wdpairs_fiber_recursion w (Down.compression i 𝒜) (Down.compression i ℬ) i,
    downComp_nonMemberSubfamily i 𝒜, downComp_memberSubfamily i 𝒜,
    downComp_nonMemberSubfamily i ℬ, downComp_memberSubfamily i ℬ]
  exact wdpairs'_fiber_downDown_ineq hw i hdom _ _ _ _












theorem wdpairs_downDown_mono_satisfiable :
    wdpairs (fun (_ : Fin 1) b => if b then (0 : ℝ) else 1)
        ({{0}} : Finset (Finset (Fin 1))) {{0}}
      ≤ wdpairs (fun (_ : Fin 1) b => if b then (0 : ℝ) else 1)
          (Down.compression 0 ({{0}} : Finset (Finset (Fin 1))))
          (Down.compression 0 ({{0}} : Finset (Finset (Fin 1)))) :=
  wdpairs_downDown_mono (fun _ b => by cases b <;> norm_num) 0 (by norm_num) _ _








theorem wdpairs_downDown_not_mono_general :
    ∃ (w : Fin 1 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 1))) (i : Fin 1),
      (∀ x b, 0 ≤ w x b) ∧
      ¬ (wdpairs w 𝒜 ℬ ≤ wdpairs w (Down.compression i 𝒜) (Down.compression i ℬ)) := by
  refine ⟨fun _ b => if b then 2 else 1, {{0}}, {∅}, 0,
    fun _ b => by cases b <;> norm_num, ?_⟩
  set w : Fin 1 → Bool → ℝ := fun _ b => if b then 2 else 1 with hw
  
  have hL : wdpairs w ({{0}} : Finset (Finset (Fin 1))) {∅} = 2 := by
    unfold wdpairs fwt
    norm_num [hw, Finset.filter_singleton, Finset.disjoint_singleton_left]
  
  have hcA : Down.compression (0 : Fin 1) ({{0}} : Finset (Finset (Fin 1))) = {∅} := by decide
  have hcB : Down.compression (0 : Fin 1) ({∅} : Finset (Finset (Fin 1))) = {∅} := by decide
  have hR : wdpairs w (Down.compression (0 : Fin 1) ({{0}} : Finset (Finset (Fin 1))))
              (Down.compression (0 : Fin 1) ({∅} : Finset (Finset (Fin 1)))) = 1 := by
    rw [hcA, hcB]
    unfold wdpairs fwt
    norm_num [hw, Finset.filter_singleton, Finset.disjoint_empty_left]
  rw [hL, hR]; norm_num
















theorem wdpairs_symm_downDown_mono {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (i : α) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ wdpairs w (Down.compression i 𝒜) (Down.compression i ℬ) := by
  rw [wdpairs_symm_eq_const_mul_count hsym, wdpairs_symm_eq_const_mul_count hsym]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact_mod_cast dpairsCount_downDown_mono 𝒜 ℬ i






theorem fmarg_symm_downComp {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (i : α) (𝒜 : Finset (Finset α)) :
    fmarg w (Down.compression i 𝒜) = fmarg w 𝒜 := by
  rw [fmarg_symm_eq_const_mul_card hsym, fmarg_symm_eq_const_mul_card hsym,
    Down.card_compression]

end Weighted

















































end StatMech
