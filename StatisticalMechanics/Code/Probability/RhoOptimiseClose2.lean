/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Code.Probability.BourgainPerCoord

open scoped BigOperators
open Finset
open Real Filter Topology
open intervalIntegral MeasureTheory

set_option linter.style.longLine false

namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem cro2_integral_exp_mul (c : ℝ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Real.exp (c * x) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hc, integral_exp]
  rw [smul_eq_mul]; field_simp



theorem cro2_integral_exp_le (t : ℝ) (ht : 0 < t) :
    (∫ u in (0:ℝ)..1, Real.exp (-(t / 2) * u)) ≤ 2 / t := by
  have hc : -(t / 2) ≠ 0 := by intro h; nlinarith
  rw [cro2_integral_exp_mul (-(t / 2)) hc 0 1]
  rw [mul_one, mul_zero, Real.exp_zero]
  have hexp : (0:ℝ) < Real.exp (-(t / 2)) := Real.exp_pos _
  have key : (Real.exp (-(t / 2)) - 1) / -(t / 2) = (1 - Real.exp (-(t / 2))) / (t / 2) := by
    field_simp; ring
  rw [key, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hexp]


theorem cro2_integral_one_sub_pow (n : ℕ) :
    ∫ u in (0:ℝ)..1, (1 - u) ^ n = 1 / (n + 1) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1) (fun x => x ^ n) 1
  simp only at h
  rw [h]
  norm_num [integral_pow]









omit [Fintype ι] [DecidableEq ι] in

theorem cro2_summand_intervalIntegrable (cf : Finset ι → ℝ) (S : Finset ι) :
    IntervalIntegrable (fun u => 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S)
      MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

omit [Fintype ι] in



theorem cro2_integral_summand (cf : Finset ι → ℝ) (S : Finset ι) :
    (∫ u in (0:ℝ)..1, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S)
      = (if S = ∅ then 0 else 4 * cf S) := by
  rw [show (fun u => 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S)
      = (fun u => (4 * (S.card : ℝ) * cf S) * (1 - u) ^ (S.card - 1)) from by funext u; ring]
  rw [intervalIntegral.integral_const_mul, cro2_integral_one_sub_pow]
  by_cases hS : S = ∅
  · subst hS; simp
  · rw [if_neg hS]
    have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have hh : (S.card - 1 : ℕ) + 1 = S.card := Nat.succ_pred_eq_of_pos hpos
    have hc1 : (↑(S.card - 1) + 1 : ℝ) = (S.card : ℝ) := by
      have := congrArg (Nat.cast (R := ℝ)) hh
      push_cast at this; linarith
    rw [hc1]
    have hcardpos : (0:ℝ) < (S.card : ℝ) := by exact_mod_cast hpos
    field_simp



theorem cro2_integral_lhs (cf : Finset ι → ℝ) :
    (∫ u in (0:ℝ)..1, ∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S)
      = 4 * ∑ S ∈ (univ.erase (∅ : Finset ι)), cf S := by
  rw [intervalIntegral.integral_finsetSum
      (fun S _ => cro2_summand_intervalIntegrable cf S)]
  simp_rw [cro2_integral_summand cf]
  rw [← Finset.add_sum_erase univ (fun S => if S = ∅ then (0:ℝ) else 4 * cf S)
      (Finset.mem_univ ∅)]
  rw [if_pos rfl, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [if_neg (Finset.ne_of_mem_erase hS)]








theorem cro2_rpow_integrable (δ : ℝ) (hδ0 : 0 < δ) :
    IntervalIntegrable (fun u => δ ^ (u / (2 - u))) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num)]
  apply ContinuousOn.congr (f := fun u => Real.exp (Real.log δ * (u / (2 - u))))
  · apply ContinuousOn.comp (g := Real.exp) Real.continuous_exp.continuousOn
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div continuousOn_id (by fun_prop)
      intro x hx
      simp only [Set.mem_Icc] at hx
      intro h; linarith [hx.2]
    · exact Set.mapsTo_univ _ _
  · intro u _; simp only; rw [Real.rpow_def_of_pos hδ0]




theorem cro2_integral_rhs_le (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u))) ≤ 2 / (-(Real.log δ)) := by
  have ht : 0 < -(Real.log δ) := by have := Real.log_neg hδ0 hδ1; linarith
  refine le_trans ?_ (cro2_integral_exp_le _ ht)
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact cro2_rpow_integrable δ hδ0
  · apply Continuous.intervalIntegrable; fun_prop
  · intro u hu
    simp only [Set.mem_Icc] at hu
    rw [Real.rpow_def_of_pos hδ0]
    apply Real.exp_le_exp.mpr
    have hlogneg : Real.log δ < 0 := Real.log_neg hδ0 hδ1
    have h2u : (0:ℝ) < 2 - u := by linarith [hu.2]
    rw [show -(-(Real.log δ) / 2) * u = Real.log δ * (u / 2) from by ring]
    apply mul_le_mul_of_nonpos_left _ (le_of_lt hlogneg)
    rw [div_le_div_iff₀ (by norm_num) h2u]
    nlinarith [hu.1]










theorem cro2_master_sub {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool)
    (Hcap : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
        (∑ S : Finset E, 4 * (S.card : ℝ) * (ρ ^ (S.card - 1)) ^ 2
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
          ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
              ^ (2 / (1 + ρ ^ 2) - 1)
            * (∑ S : Finset E, 4 * (S.card : ℝ)
                * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2))
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * (∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) := by
  have hu1' : (0:ℝ) ≤ 1 - u := by linarith
  set ρ := Real.sqrt (1 - u) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hρsq : ρ ^ 2 = 1 - u := Real.sq_sqrt hu1'
  have H := Hcap ρ hρ0 hρ1
  have hpow : ∀ S : Finset E, (ρ ^ (S.card - 1)) ^ 2 = (1 - u) ^ (S.card - 1) := by
    intro S; rw [← pow_mul, mul_comm, pow_mul, hρsq]
  have hexp : (2:ℝ) / (1 + ρ ^ 2) - 1 = u / (2 - u) := by
    rw [hρsq]
    have h1 : (1:ℝ) + (1 - u) = 2 - u := by ring
    rw [h1, div_sub_one (by linarith : (2:ℝ) - u ≠ 0)]
    ring_nf
  rw [hexp] at H
  simp_rw [hpow] at H
  exact H




















theorem cro2_rhoOptimise : bph_RhoOptimise 2 := by
  intro E _ _ _ φ Hcap
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set cf := fun S : Finset E => (khc_fourierCoeff f S) ^ 2 with hcf
  set δ := maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f with hδ
  set V := ∑ S ∈ (univ.erase (∅ : Finset E)), cf S with hV
  set W := ∑ S : Finset E, 4 * (S.card : ℝ) * cf S with hW
  
  have hWnn : 0 ≤ W := by
    rw [hW]; exact Finset.sum_nonneg (fun S _ => by positivity)
  have hVnn : 0 ≤ V := by rw [hV]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hδnn : 0 ≤ δ := by
    rw [hδ]
    exact kkl_maxInfl_nonneg
      (OSSS.bernoulliWeight_isProbWeight (E := E) (by norm_num) (by norm_num)) f
  
  show 2 * V * Real.log (1 / δ) ≤ W
  
  rcases lt_trichotomy δ 1 with hδ1 | hδ1 | hδ1
  · 
    rcases eq_or_lt_of_le hδnn with hδ0 | hδ0
    · 
      rw [← hδ0, div_zero, Real.log_zero, mul_zero]; exact hWnn
    · 
      have ht : 0 < -(Real.log δ) := by have := Real.log_neg hδ0 hδ1; linarith
      have hlogeq : Real.log (1 / δ) = -(Real.log δ) := by
        rw [Real.log_div one_ne_zero (ne_of_gt hδ0), Real.log_one, zero_sub]
      
      have hIntLhs : (∫ u in (0:ℝ)..1, ∑ S : Finset E, 4 * (S.card : ℝ)
          * (1 - u) ^ (S.card - 1) * cf S) = 4 * V := by
        rw [cro2_integral_lhs cf]
      
      have hIntRhs : (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u)) * W) ≤ W * (2 / (-(Real.log δ))) := by
        rw [intervalIntegral.integral_mul_const]
        rw [mul_comm W _]
        apply mul_le_mul_of_nonneg_right (cro2_integral_rhs_le δ hδ0 hδ1) hWnn
      
      have hmono : (∫ u in (0:ℝ)..1, ∑ S : Finset E, 4 * (S.card : ℝ)
            * (1 - u) ^ (S.card - 1) * cf S)
          ≤ (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u)) * W) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · apply Continuous.intervalIntegrable; fun_prop
        · exact (cro2_rpow_integrable δ hδ0).mul_const W
        · intro u hu
          simp only [Set.mem_Icc] at hu
          have := cro2_master_sub φ Hcap u hu.1 hu.2
          calc (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * cf S)
              = (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
                  * (khc_fourierCoeff f S) ^ 2) := by
                apply Finset.sum_congr rfl; intro S _; rw [hcf]
            _ ≤ δ ^ (u / (2 - u)) * W := this
      rw [hIntLhs] at hmono
      have hfin : 4 * V ≤ W * (2 / (-(Real.log δ))) := le_trans hmono hIntRhs
      rw [hlogeq]
      
      rw [mul_div_assoc'] at hfin
      rw [le_div_iff₀ ht] at hfin
      nlinarith [hfin, ht]
  · 
    rw [hδ1, div_one, Real.log_one, mul_zero]; exact hWnn
  · 
    have hlog : Real.log (1 / δ) ≤ 0 := by
      rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub, neg_nonpos]
      exact Real.log_nonneg (by linarith)
    nlinarith [hVnn, hWnn, hlog]

end StatMech.Probability
