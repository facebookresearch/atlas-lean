/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Code.Inequalities.ReimerButterflyClose

open Finset
open scoped FinsetFamily

namespace StatMech

variable {α : Type*} [DecidableEq α]

section Weighted

variable [Fintype α]























theorem wbutterfly_deficit_identity (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    fmarg w 𝒜 * fmarg w ℬ - wdpairs w 𝒜 ℬ
      = w i true * w i true
          * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i))
      + w i true * w i false
          * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.nonMemberSubfamily i)
              - wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i))
      + w i false * w i true
          * (fmarg' w i (𝒜.nonMemberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i)
              - wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i))
      + w i false * w i false
          * (fmarg' w i (𝒜.nonMemberSubfamily i) * fmarg' w i (ℬ.nonMemberSubfamily i)
              - wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
  have hrec := wdpairs_fiber_recursion w 𝒜 ℬ i
  have hA := fmarg_split w 𝒜 i
  have hB := fmarg_split w ℬ i
  rw [hrec, hA, hB]
  ring







theorem wbutterfly_gap_ge_member {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b)
    (𝒜 ℬ : Finset (Finset α)) (i : α) :
    wdpairs w 𝒜 ℬ
        + w i true * w i true
            * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i))
      ≤ fmarg w 𝒜 * fmarg w ℬ := by
  have hid := wbutterfly_deficit_identity w 𝒜 ℬ i
  have hMN := wdpairs'_le_mul hw i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
  have hNM := wdpairs'_le_mul hw i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)
  have hNN := wdpairs'_le_mul hw i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
  have h0 := hw i false
  have h1 := hw i true
  nlinarith [hid, mul_nonneg h1 h0, mul_nonneg h0 h1, mul_nonneg h0 h0,
    sub_nonneg.mpr hMN, sub_nonneg.mpr hNM, sub_nonneg.mpr hNN]













theorem fwt_symm_eq_const {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (S : Finset α) : fwt w S = ∏ x, w x true := by
  unfold fwt
  apply Finset.prod_congr rfl
  intro x _
  cases h : decide (x ∈ S) with
  | false => rw [hsym x]
  | true => rfl




theorem fmarg_symm_eq_const_mul_card {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (𝒜 : Finset (Finset α)) :
    fmarg w 𝒜 = (∏ x, w x true) * (𝒜.card : ℝ) := by
  unfold fmarg
  rw [Finset.sum_congr rfl (fun S _ => fwt_symm_eq_const hsym S)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]





theorem wdpairs_symm_eq_const_mul_count {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ = (∏ x, w x true) ^ 2 * (dpairsCount 𝒜 ℬ : ℝ) := by
  unfold wdpairs dpairsCount
  rw [Finset.sum_congr rfl (fun p _ => by
    rw [fwt_symm_eq_const hsym p.1, fwt_symm_eq_const hsym p.2])]
  rw [Finset.sum_const, nsmul_eq_mul, sq]
  ring






theorem wdpairs_symm_le_mul {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
  rw [wdpairs_symm_eq_const_mul_count hsym, fmarg_symm_eq_const_mul_card hsym,
    fmarg_symm_eq_const_mul_card hsym]
  have hc : (0 : ℝ) ≤ (∏ x, w x true) ^ 2 := sq_nonneg _
  have hcount : (dpairsCount 𝒜 ℬ : ℝ) ≤ (𝒜.card : ℝ) * (ℬ.card : ℝ) := by
    have := dpairsCount_le_mul 𝒜 ℬ
    calc (dpairsCount 𝒜 ℬ : ℝ) ≤ ((𝒜.card * ℬ.card : ℕ) : ℝ) := by exact_mod_cast this
      _ = (𝒜.card : ℝ) * (ℬ.card : ℝ) := by push_cast; ring
  calc (∏ x, w x true) ^ 2 * (dpairsCount 𝒜 ℬ : ℝ)
      ≤ (∏ x, w x true) ^ 2 * ((𝒜.card : ℝ) * (ℬ.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcount hc
    _ = (∏ x, w x true) * (𝒜.card : ℝ) * ((∏ x, w x true) * (ℬ.card : ℝ)) := by ring














noncomputable def wboxValue (w : α → Bool → ℝ) (𝒰 : Finset (Finset (α ⊕ α))) : ℝ :=
  (∏ x, w x true) ^ 2 * (𝒰.card : ℝ)



theorem wdpairs_symm_eq_wboxValue {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ = wboxValue w (boxDoubled 𝒜 ℬ) := by
  rw [wdpairs_symm_eq_const_mul_count hsym, wboxValue, card_boxDoubled_eq_dpairsCount]





theorem wboxValue_doubleCompress_invariant (w : α → Bool → ℝ) (i : α)
    (𝒰 : Finset (Finset (α ⊕ α))) :
    wboxValue w (doubleCompress i 𝒰) = wboxValue w 𝒰 := by
  unfold wboxValue
  rw [doubleCompress_card]





theorem wdpairs_symm_compress_invariant {w : α → Bool → ℝ} (hsym : ∀ x, w x false = w x true)
    (i : α) (𝒜 ℬ : Finset (Finset α)) :
    wboxValue w (doubleCompress i (boxDoubled 𝒜 ℬ)) = wdpairs w 𝒜 ℬ := by
  rw [wboxValue_doubleCompress_invariant, ← wdpairs_symm_eq_wboxValue hsym]











section RefutationFixedConstant






theorem wdpairs_not_le_wboxValue_general :
    ∃ (w : Fin 1 → Bool → ℝ),
      (∀ x b, 0 ≤ w x b) ∧
      ¬ (wdpairs w ({∅} : Finset (Finset (Fin 1))) {∅}
          ≤ wboxValue w (boxDoubled ({∅} : Finset (Finset (Fin 1))) {∅})) := by
  refine ⟨fun _ b => if b then 1 else 2, fun _ b => by cases b <;> norm_num, ?_⟩
  
  have hwd : wdpairs (fun _ b => if b then (1 : ℝ) else 2) ({∅} : Finset (Finset (Fin 1))) {∅}
      = 4 := by
    unfold wdpairs fwt
    norm_num [Finset.filter_singleton, Finset.disjoint_empty_left]
  
  have hbox : (boxDoubled ({∅} : Finset (Finset (Fin 1))) {∅}).card = 1 := by
    rw [card_boxDoubled_eq_dpairsCount]
    unfold dpairsCount
    norm_num [Finset.filter_singleton, Finset.disjoint_empty_left]
  have hwb : wboxValue (fun _ b => if b then (1 : ℝ) else 2)
      (boxDoubled ({∅} : Finset (Finset (Fin 1))) {∅}) = 1 := by
    unfold wboxValue
    rw [hbox]
    norm_num
  rw [hwd, hwb]; norm_num

end RefutationFixedConstant





































end Weighted

end StatMech
