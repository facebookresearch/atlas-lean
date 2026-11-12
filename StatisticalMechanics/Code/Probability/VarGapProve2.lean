/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Code.Probability.VarGapProve
import Code.Probability.TwoPointHCqGt2

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem vgp2_degWeight_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = 4 * (ptn_sigma p) ^ 2
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set c := fun S : Finset ι => (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 with hc
  have hσ2ne : (ptn_sigma p) ^ 2 ≠ 0 := (pow_pos (ptn_sigma_pos hp0 hp1) 2).ne'
  rw [ptn_totalInfl_eq_fourierWeight hp0 hp1]
  rw [show 4 * (ptn_sigma p) ^ 2 * (1 / (ptn_sigma p) ^ 2 * ∑ S : Finset ι, (S.card : ℝ) * c S)
      = (4 * ((ptn_sigma p) ^ 2 / (ptn_sigma p) ^ 2)) * ∑ S : Finset ι, (S.card : ℝ) * c S from by
        ring]
  rw [div_self hσ2ne, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _; rw [hc]; ring


theorem vgp2_degWeight_eq_half (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      = totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  rw [vgp2_degWeight_eq hp0 hp1 φ, ptn_sigma_sq hp0 hp1]
  norm_num











theorem vgp2_master_half [Nonempty ι] (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * (∑ S : Finset ι, 4 * (S.card : ℝ)
            * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  
  rw [vgp2_degWeight_eq_half φ]
  rcases eq_or_lt_of_le hu0 with hu0' | hu0'
  · 
    rw [← hu0']
    have hbnd := frh_at_zero hp0 hp1 φ
    rw [show (0:ℝ) / (2 - 0) = 0 by norm_num, Real.rpow_zero, one_mul]
    exact hbnd
  · rcases eq_or_lt_of_le hu1 with hu1' | hu1'
    · 
      rw [hu1']
      exact frh_endpoint_one hp0 hp1 φ
    · 
      exact hcq_smallDelta_p_half φ hu0' hu1'





theorem vgp2_filter_card_ne_zero :
    (univ.filter (fun S : Finset ι => S.card ≠ 0)) = univ.erase (∅ : Finset ι) := by
  ext S
  rw [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨_, hcard⟩
    exact ⟨fun he => hcard (by rw [he, Finset.card_empty]), Finset.mem_univ S⟩
  · rintro ⟨hne, _⟩
    exact ⟨Finset.mem_univ S, fun hcard => hne (Finset.card_eq_zero.mp hcard)⟩




















theorem vgp2_kkl_logGain_half [Nonempty ι] (φ : ConfigSpace ι → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
            (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f with hδ
  
  have hc : ∀ S : Finset ι, 0 ≤ (ptn_coeff (1 / 2 : ℝ) f S) ^ 2 := fun S => sq_nonneg _
  have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hgain := roe_logGain_four (ι := Finset ι) (d := fun S => S.card)
    (c := fun S => (ptn_coeff (1 / 2 : ℝ) f S) ^ 2) hc hδnn
    (fun u hu0 hu1 => vgp2_master_half φ hu0 hu1)
  
  rw [vgp2_filter_card_ne_zero] at hgain
  
  rw [← ptn_var_eq_fourierWeight hp0 hp1 f] at hgain
  rw [vgp2_degWeight_eq_half φ] at hgain
  have hvar : OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) f
      = OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) f
        * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) f) := by
    rw [mil_var_eq φ]; ring
  rw [hvar] at hgain
  exact hgain



















theorem vgp2_logGain_flex {κ : Type*} [Fintype κ] {d : κ → ℕ} {c : κ → ℝ}
    (hc : ∀ i, 0 ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ) {B : ℝ} (hB : 0 ≤ B)
    (Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (∑ i : κ, 4 * (d i : ℝ) * (1 - u) ^ (d i - 1) * c i) ≤ δ ^ (u / (2 - u)) * B) :
    2 * (∑ i ∈ univ.filter (fun i => d i ≠ 0), c i) * Real.log (1 / δ) ≤ B := by
  
  set c' : κ → ℝ := fun i => 4 * c i with hc'
  have hc'nn : ∀ i, 0 ≤ c' i := fun i => by rw [hc']; exact mul_nonneg (by norm_num) (hc i)
  have hlhs_eq : ∀ u : ℝ, roe_lhs d c' u = ∑ i : κ, 4 * (d i : ℝ) * (1 - u) ^ (d i - 1) * c i := by
    intro u; unfold roe_lhs; apply Finset.sum_congr rfl; intro i _; rw [hc']; ring
  have hVeq : roe_V d c' = 4 * ∑ i ∈ univ.filter (fun i => d i ≠ 0), c i := by
    unfold roe_V; rw [Finset.mul_sum]
  set V4 : ℝ := 4 * ∑ i ∈ univ.filter (fun i => d i ≠ 0), c i with hV4
  rcases lt_trichotomy δ 1 with hδ1 | hδ1 | hδ1
  · rcases eq_or_lt_of_le hδ with hδ0 | hδ0
    · 
      rw [← hδ0, div_zero, Real.log_zero, mul_zero]; exact hB
    · 
      have ht : 0 < -(Real.log δ) := by have := Real.log_neg hδ0 hδ1; linarith
      have hlogeq : Real.log (1 / δ) = -(Real.log δ) := by
        rw [Real.log_div one_ne_zero (ne_of_gt hδ0), Real.log_one, zero_sub]
      
      have hIntLhs : (∫ u in (0:ℝ)..1, roe_lhs d c' u) = V4 := by
        rw [roe_integral_lhs d c', hVeq, hV4]
      
      have hIntRhs : (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u)) * B) ≤ B * (2 / (-(Real.log δ))) := by
        rw [intervalIntegral.integral_mul_const, mul_comm B _]
        exact mul_le_mul_of_nonneg_right (roe_integral_rhs_le δ hδ0 hδ1) hB
      
      have hmono : (∫ u in (0:ℝ)..1, roe_lhs d c' u)
          ≤ (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u)) * B) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · unfold roe_lhs
          apply Continuous.intervalIntegrable; fun_prop
        · exact (roe_rpow_integrable δ hδ0).mul_const B
        · intro u hu
          simp only [Set.mem_Icc] at hu
          rw [hlhs_eq u]
          exact Hmaster u hu.1 hu.2
      rw [hIntLhs] at hmono
      have hfin : V4 ≤ B * (2 / (-(Real.log δ))) := le_trans hmono hIntRhs
      rw [hV4] at hfin
      rw [hlogeq]
      
      rw [mul_div_assoc'] at hfin
      rw [le_div_iff₀ ht] at hfin
      nlinarith [hfin, ht]
  · 
    rw [hδ1, div_one, Real.log_one, mul_zero]; exact hB
  · 
    have hVnn : 0 ≤ ∑ i ∈ univ.filter (fun i => d i ≠ 0), c i :=
      Finset.sum_nonneg (fun i _ => hc i)
    have hlog : Real.log (1 / δ) ≤ 0 := by
      rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub, neg_nonpos]
      exact Real.log_nonneg (by linarith)
    nlinarith [hVnn, hB, hlog]
















theorem vgp2_kkl_logGain_of_master {q : ℝ} (H : frh_openResidue q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hp0 : 0 < p := by have := hp.1; linarith
  set f := fun ω : ConfigSpace E => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hc : ∀ S : Finset E, 0 ≤ (ptn_coeff p f S) ^ 2 := fun S => sq_nonneg _
  
  have Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p f S) ^ 2)
        ≤ δ ^ (u / (2 - u)) * T := by
    intro u hu0 hu1
    rcases eq_or_lt_of_le hu0 with hu0' | hu0'
    · rw [← hu0']
      rw [show (0:ℝ) / (2 - 0) = 0 by norm_num, Real.rpow_zero, one_mul]
      exact frh_at_zero hp0 hp1 φ
    · rcases eq_or_lt_of_le hu1 with hu1' | hu1'
      · rw [hu1']; exact frh_endpoint_one hp0 hp1 φ
      · exact H p hp hp1 φ u hu0' hu1'
  
  have hgain := vgp2_logGain_flex (κ := Finset E) (d := fun S => S.card)
    (c := fun S => (ptn_coeff p f S) ^ 2) hc hδnn hTnn Hmaster
  rw [vgp2_filter_card_ne_zero] at hgain
  rw [← ptn_var_eq_fourierWeight hp0 hp1 f] at hgain
  have hvar : OSSS.var (OSSS.bernoulliWeight p) f
      = OSSS.expect (OSSS.bernoulliWeight p) f * (1 - OSSS.expect (OSSS.bernoulliWeight p) f) := by
    rw [mil_var_eq φ]; ring
  rw [hvar] at hgain
  exact hgain











theorem vgp2_var_le_half [Nonempty ι] (φ : ConfigSpace ι → Bool)
    (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδ1 : maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) < 1) :
    OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
        * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
            (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
          / (2 * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0))) := by
  set δ := maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) with hδ
  set Var := OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
      with hVar
  set T := totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) with hT
  have hgain := vgp2_kkl_logGain_half φ
  rw [← hδ, ← hVar, ← hT] at hgain
  
  have hlog : 0 < Real.log (1 / δ) := by
    rw [Real.log_pos_iff (by positivity)]; rw [lt_div_iff₀ hδ0]; linarith
  
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hgain, hlog]








theorem vgp2_logGain_dictator :
    2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
            (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω : ConfigSpace (Fin 1) => if (fun ω => ω 0) ω then (1 : ℝ) else 0) :=
  vgp2_kkl_logGain_half (fun ω => ω 0)






theorem vgp2_logGain_const_nonvacuous [Nonempty ι] :
    2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
            (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if (fun _ => false : ConfigSpace ι → Bool) ω then (1 : ℝ) else 0) :=
  vgp2_kkl_logGain_half (fun _ => false)

end StatMech.Probability
