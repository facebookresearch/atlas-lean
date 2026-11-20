/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Code.Probability.PBiasedTensorize
import Code.Probability.RhoOptimiseClose2
import Code.Probability.MaxElementDecomp

open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





noncomputable def frh_perCoordWeight (p u : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
    (Real.sqrt (1 - u) ^ (S.erase e).card) ^ 2
      * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2




theorem frh_lhs_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = 4 * (ptn_sigma p) ^ 2 * ∑ e : ι, frh_perCoordWeight p u φ e := by
  have hu1' : (0:ℝ) ≤ 1 - u := by linarith
  set cc := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hcc
  have hσ2 : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  have hσ2sq : (0:ℝ) < (ptn_sigma p)^2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  set ρ := Real.sqrt (1 - u) with hρ
  have hρsq : ρ ^ 2 = 1 - u := Real.sq_sqrt hu1'
  have hWe : ∀ e : ι, frh_perCoordWeight p u φ e
      = (1 / (ptn_sigma p)^2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
          (ρ ^ (S.erase e).card) ^ 2 * cc S := by
    intro e
    unfold frh_perCoordWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hcc, div_pow, one_div, hρ]; ring
  simp_rw [hWe]
  rw [← Finset.mul_sum]
  rw [show 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p)^2) * ∑ e : ι, ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * cc S)
      = 4 * ∑ e : ι, ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * cc S from by field_simp]
  rw [Finset.mul_sum]
  have hinner : ∀ e : ι, (∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ρ ^ (S.erase e).card) ^ 2 * cc S)
      = ∑ S : Finset ι, (if e ∈ S then (ρ ^ (S.card - 1)) ^ 2 * cc S else 0) := by
    intro e
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases he : e ∈ S
    · rw [if_pos he, if_pos he, Finset.card_erase_of_mem he]
    · rw [if_neg he, if_neg he]
  simp_rw [hinner]
  rw [show (∑ e : ι, 4 * ∑ S : Finset ι, (if e ∈ S then (ρ ^ (S.card - 1)) ^ 2 * cc S else 0))
      = ∑ e : ι, ∑ S : Finset ι, (if e ∈ S then 4 * ((ρ ^ (S.card - 1)) ^ 2 * cc S) else 0) from by
        apply Finset.sum_congr rfl; intro e _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro S _; by_cases he : e ∈ S <;> simp [he]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [show (ρ ^ (S.card - 1)) ^ 2 = (1 - u) ^ (S.card - 1) from by rw [← pow_mul, mul_comm, pow_mul, hρsq]]
  ring


theorem frh_perCoordWeight_nonneg (p u : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) :
    0 ≤ frh_perCoordWeight p u φ e := by
  unfold frh_perCoordWeight
  exact Finset.sum_nonneg (fun S _ => by positivity)






theorem frh_at_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (0:ℝ)) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set cc := fun S : Finset ι => (ptn_coeff p f S) ^ 2 with hcc
  have hσ2val : (ptn_sigma p)^2 = p*(1-p) := ptn_sigma_sq hp0 hp1
  have hσ2sq : (0:ℝ) < (ptn_sigma p)^2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hσ2ne : (ptn_sigma p)^2 ≠ 0 := ne_of_gt hσ2sq
  
  rw [ptn_totalInfl_eq_fourierWeight hp0 hp1]
  
  have hLHS : (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (0:ℝ)) ^ (S.card - 1) * cc S)
      = 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [show (1 : ℝ) - 0 = 1 by norm_num, one_pow]
    rw [show 4 * (ptn_sigma p)^2 * (1 / (ptn_sigma p)^2 * ((S.card : ℝ) * cc S))
        = (4 * ((S.card : ℝ) * cc S)) * ((ptn_sigma p)^2 / (ptn_sigma p)^2) from by ring]
    rw [div_self hσ2ne, mul_one]; ring
  rw [hLHS]
  have hsumnn : 0 ≤ (1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun S _ => by positivity)
  have h4σ : 4 * (ptn_sigma p)^2 ≤ 1 := by rw [hσ2val]; nlinarith [sq_nonneg (1 - 2*p)]
  calc 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S)
      ≤ 1 * ((1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S) :=
        mul_le_mul_of_nonneg_right h4σ hsumnn
    _ = (1 / (ptn_sigma p)^2) * ∑ S : Finset ι, (S.card : ℝ) * cc S := by rw [one_mul]













theorem frh_capped_martingale [Nonempty ι] {p q' : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : 1 ≤ q') (hq2 : q' ≤ 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p)) (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * (ptn_sigma p) ^ 2
        * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  have hu1' : (0:ℝ) ≤ 1 - u := by linarith
  set ρ := Real.sqrt (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hρsq : ρ ^ 2 = (q' - 1) * 4 * p * (1 - p) := by rw [Real.sq_sqrt hu1']; exact hrel
  have hcap := ptn_capped_hc hp0 hp1 hρ0 hρ1 hq1 hq2 hρsq φ
  have hσ2sq : (0:ℝ) < (ptn_sigma p)^2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hσne : ptn_sigma p ≠ 0 := (ptn_sigma_pos hp0 hp1).ne'
  set cc := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hcc
  have hpow : ∀ S : Finset ι, (ρ ^ (S.card - 1)) ^ 2 = (1 - u) ^ (S.card - 1) := by
    intro S; rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hu1']
  have hLHS : (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cc S)
      = 4 * (ptn_sigma p)^2 * ((1 / (ptn_sigma p) ^ 2) * ∑ S : Finset ι, (S.card : ℝ) * ((ρ ^ (S.card - 1)) ^ 2 * cc S)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [hpow S]
    field_simp
  rw [hLHS]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hcap





theorem frh_capped_param {p u : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hlo : 1 - 4 * p * (1 - p) ≤ u) (hu1 : u ≤ 1) :
    ∃ q' : ℝ, 1 ≤ q' ∧ q' ≤ 2 ∧ 1 - u = (q' - 1) * 4 * p * (1 - p) := by
  have hs : 0 < 4 * p * (1 - p) := by nlinarith
  refine ⟨1 + (1 - u) / (4 * p * (1 - p)), ?_, ?_, ?_⟩
  · have : 0 ≤ (1 - u) / (4 * p * (1 - p)) := by
      apply div_nonneg (by linarith) (by linarith)
    linarith
  · 
    have : (1 - u) / (4 * p * (1 - p)) ≤ 1 := by
      rw [div_le_one hs]; linarith
    linarith
  · 
    rw [show (1 + (1 - u) / (4 * p * (1 - p)) - 1) * 4 * p * (1 - p)
        = ((1 - u) / (4 * p * (1 - p))) * (4 * p * (1 - p)) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt hs)]






























def frh_openResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool), ∀ u : ℝ, 0 < u → u < 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)





theorem frh_endpoint_one [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (1:ℝ)) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((1:ℝ) / (2 - 1))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hcap := frh_capped_martingale hp0 hp1 (le_refl (1:ℝ)) (by norm_num : (1:ℝ) ≤ 2)
    (by norm_num : (0:ℝ) ≤ 1) (le_refl (1:ℝ)) (by ring) φ
  
  have hδnn : 0 ≤ δ := by rw [hδ]; exact kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hTnn : 0 ≤ T := by rw [hT]; exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hσ2val : (ptn_sigma p)^2 = p*(1-p) := ptn_sigma_sq hp0 hp1
  have h4σ : 4 * (ptn_sigma p)^2 ≤ 1 := by rw [hσ2val]; nlinarith [sq_nonneg (1 - 2*p)]
  have hσnn : (0:ℝ) ≤ 4 * (ptn_sigma p)^2 := by positivity
  have hexp1 : (2:ℝ) / 1 - 1 = (1:ℝ) / (2 - 1) := by norm_num
  have hRHSnn : 0 ≤ δ ^ ((2:ℝ)/1 - 1) * T := by positivity
  refine le_trans hcap ?_
  calc 4 * (ptn_sigma p)^2 * (δ ^ ((2:ℝ)/1 - 1) * T)
      ≤ 1 * (δ ^ ((2:ℝ)/1 - 1) * T) := mul_le_mul_of_nonneg_right h4σ hRHSnn
    _ = δ ^ ((2:ℝ)/1 - 1) * T := by rw [one_mul]
    _ = δ ^ ((1:ℝ) / (2 - 1)) * T := by rw [hexp1]





theorem frh_martingaleHC_of_openResidue {q : ℝ} (H : frh_openResidue q) :
    mxd_martingaleHC_statement q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  rcases eq_or_lt_of_le hu0 with hu0' | hu0'
  · 
    subst hu0'
    have hbnd := frh_at_zero hp0 hp1 φ
    rw [show (0:ℝ) / (2 - 0) = 0 by norm_num, Real.rpow_zero, one_mul]
    exact hbnd
  · 
    rcases eq_or_lt_of_le hu1 with hu1' | hu1'
    · 
      subst hu1'
      exact frh_endpoint_one hp0 hp1 φ
    · 
      exact H p hp hp1 φ u hu0' hu1'








theorem frh_lowNoise_range_nonempty {p : ℝ} (hp : 1 / 2 < p) (_hp1 : p < 1) :
    0 < 1 - 4 * p * (1 - p) := by
  have heq : 1 - 4 * p * (1 - p) = (1 - 2 * p) ^ 2 := by ring
  rw [heq]
  have hne : (1 - 2 * p) ≠ 0 := by intro h; nlinarith [h]
  positivity




theorem frh_openResidue_c0 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (u : ℝ) :
    (∑ S : Finset E, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hzero : (∑ S : Finset E, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
      * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 0 := by
    apply Finset.sum_eq_zero; intro S _; ring
  rw [hzero]
  have hδnn : 0 ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
    kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _
  have hTnn : 0 ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
    kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _
  positivity

end StatMech.Probability
