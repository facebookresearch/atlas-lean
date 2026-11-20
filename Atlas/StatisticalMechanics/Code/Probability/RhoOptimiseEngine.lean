/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib

open scoped BigOperators
open Finset
open Real Filter Topology
open intervalIntegral MeasureTheory

set_option linter.style.longLine false

namespace StatMech.Probability




theorem roe_integral_exp_mul (c : ℝ) (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, Real.exp (c * x) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) hc, integral_exp]
  rw [smul_eq_mul]; field_simp


theorem roe_integral_exp_le (t : ℝ) (ht : 0 < t) :
    (∫ u in (0:ℝ)..1, Real.exp (-(t / 2) * u)) ≤ 2 / t := by
  have hc : -(t / 2) ≠ 0 := by intro h; nlinarith
  rw [roe_integral_exp_mul (-(t / 2)) hc 0 1]
  rw [mul_one, mul_zero, Real.exp_zero]
  have hexp : (0:ℝ) < Real.exp (-(t / 2)) := Real.exp_pos _
  have key : (Real.exp (-(t / 2)) - 1) / -(t / 2) = (1 - Real.exp (-(t / 2))) / (t / 2) := by
    field_simp; ring
  rw [key, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hexp]


theorem roe_integral_one_sub_pow (n : ℕ) :
    ∫ u in (0:ℝ)..1, (1 - u) ^ n = 1 / (n + 1) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1) (fun x => x ^ n) 1
  simp only at h
  rw [h]
  norm_num [integral_pow]


theorem roe_rpow_integrable (δ : ℝ) (hδ0 : 0 < δ) :
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


theorem roe_integral_rhs_le (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u))) ≤ 2 / (-(Real.log δ)) := by
  have ht : 0 < -(Real.log δ) := by have := Real.log_neg hδ0 hδ1; linarith
  refine le_trans ?_ (roe_integral_exp_le _ ht)
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact roe_rpow_integrable δ hδ0
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














variable {ι : Type*} [Fintype ι]



noncomputable def roe_lhs (d : ι → ℕ) (c : ι → ℝ) (u : ℝ) : ℝ :=
  ∑ i : ι, (d i : ℝ) * (1 - u) ^ (d i - 1) * c i


noncomputable def roe_W (d : ι → ℕ) (c : ι → ℝ) : ℝ :=
  ∑ i : ι, (d i : ℝ) * c i


noncomputable def roe_V (d : ι → ℕ) (c : ι → ℝ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => d i ≠ 0), c i


theorem roe_W_nonneg {d : ι → ℕ} {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    0 ≤ roe_W d c :=
  Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hc i)


theorem roe_V_nonneg {d : ι → ℕ} {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    0 ≤ roe_V d c :=
  Finset.sum_nonneg fun i _ => hc i

omit [Fintype ι] in

theorem roe_summand_intervalIntegrable (d : ι → ℕ) (c : ι → ℝ) (i : ι) :
    IntervalIntegrable (fun u => (d i : ℝ) * (1 - u) ^ (d i - 1) * c i)
      MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable; fun_prop

omit [Fintype ι] in



theorem roe_integral_summand (d : ι → ℕ) (c : ι → ℝ) (i : ι) :
    (∫ u in (0:ℝ)..1, (d i : ℝ) * (1 - u) ^ (d i - 1) * c i)
      = (if d i = 0 then 0 else c i) := by
  rw [show (fun u => (d i : ℝ) * (1 - u) ^ (d i - 1) * c i)
      = (fun u => ((d i : ℝ) * c i) * (1 - u) ^ (d i - 1)) from by funext u; ring]
  rw [intervalIntegral.integral_const_mul, roe_integral_one_sub_pow]
  by_cases hi : d i = 0
  · rw [if_pos hi, hi]; simp
  · rw [if_neg hi]
    have hpos : 0 < d i := Nat.pos_of_ne_zero hi
    have hh : (d i - 1 : ℕ) + 1 = d i := Nat.succ_pred_eq_of_pos hpos
    have hc1 : (↑(d i - 1) + 1 : ℝ) = (d i : ℝ) := by
      have := congrArg (Nat.cast (R := ℝ)) hh
      push_cast at this; linarith
    rw [hc1]
    have hcardpos : (0:ℝ) < (d i : ℝ) := by exact_mod_cast hpos
    field_simp



theorem roe_integral_lhs (d : ι → ℕ) (c : ι → ℝ) :
    (∫ u in (0:ℝ)..1, roe_lhs d c u) = roe_V d c := by
  unfold roe_lhs roe_V
  rw [intervalIntegral.integral_finsetSum
      (fun i _ => roe_summand_intervalIntegrable d c i)]
  rw [show (∑ i : ι, ∫ u in (0:ℝ)..1, (d i : ℝ) * (1 - u) ^ (d i - 1) * c i)
      = ∑ i : ι, (if d i = 0 then (0:ℝ) else c i) from by
    apply Finset.sum_congr rfl; intro i _; rw [roe_integral_summand]]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]



























theorem roe_logGain {d : ι → ℕ} {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ)
    (Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → roe_lhs d c u ≤ δ ^ (u / (2 - u)) * roe_W d c) :
    roe_V d c * Real.log (1 / δ) ≤ 2 * roe_W d c := by
  set W := roe_W d c with hW
  set V := roe_V d c with hV
  have hWnn : 0 ≤ W := roe_W_nonneg hc
  have hVnn : 0 ≤ V := roe_V_nonneg hc
  rcases lt_trichotomy δ 1 with hδ1 | hδ1 | hδ1
  · rcases eq_or_lt_of_le hδ with hδ0 | hδ0
    · 
      rw [← hδ0, div_zero, Real.log_zero, mul_zero]; linarith
    · 
      have ht : 0 < -(Real.log δ) := by have := Real.log_neg hδ0 hδ1; linarith
      have hlogeq : Real.log (1 / δ) = -(Real.log δ) := by
        rw [Real.log_div one_ne_zero (ne_of_gt hδ0), Real.log_one, zero_sub]
      
      have hIntLhs : (∫ u in (0:ℝ)..1, roe_lhs d c u) = V := roe_integral_lhs d c
      
      have hIntRhs : (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u)) * W) ≤ W * (2 / (-(Real.log δ))) := by
        rw [intervalIntegral.integral_mul_const, mul_comm W _]
        exact mul_le_mul_of_nonneg_right (roe_integral_rhs_le δ hδ0 hδ1) hWnn
      
      have hmono : (∫ u in (0:ℝ)..1, roe_lhs d c u)
          ≤ (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u)) * W) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · unfold roe_lhs
          apply Continuous.intervalIntegrable; fun_prop
        · exact (roe_rpow_integrable δ hδ0).mul_const W
        · intro u hu
          simp only [Set.mem_Icc] at hu
          exact Hmaster u hu.1 hu.2
      rw [hIntLhs] at hmono
      have hfin : V ≤ W * (2 / (-(Real.log δ))) := le_trans hmono hIntRhs
      rw [hlogeq]
      
      rw [mul_div_assoc'] at hfin
      rw [le_div_iff₀ ht] at hfin
      nlinarith [hfin, ht]
  · 
    rw [hδ1, div_one, Real.log_one, mul_zero]; linarith
  · 
    have hlog : Real.log (1 / δ) ≤ 0 := by
      rw [Real.log_div one_ne_zero (by linarith), Real.log_one, zero_sub, neg_nonpos]
      exact Real.log_nonneg (by linarith)
    nlinarith [hVnn, hWnn, hlog]


















theorem roe_logGain_four {d : ι → ℕ} {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {δ : ℝ} (hδ : 0 ≤ δ)
    (Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (∑ i : ι, 4 * (d i : ℝ) * (1 - u) ^ (d i - 1) * c i)
        ≤ δ ^ (u / (2 - u)) * (∑ i : ι, 4 * (d i : ℝ) * c i)) :
    2 * (∑ i ∈ univ.filter (fun i => d i ≠ 0), c i) * Real.log (1 / δ)
      ≤ ∑ i : ι, 4 * (d i : ℝ) * c i := by
  
  set c' : ι → ℝ := fun i => 4 * c i with hc'
  have hc'nn : ∀ i, 0 ≤ c' i := fun i => by rw [hc']; exact mul_nonneg (by norm_num) (hc i)
  have hWeq : roe_W d c' = ∑ i : ι, 4 * (d i : ℝ) * c i := by
    unfold roe_W; apply Finset.sum_congr rfl; intro i _; rw [hc']; ring
  have hVeq : roe_V d c' = 4 * ∑ i ∈ univ.filter (fun i => d i ≠ 0), c i := by
    unfold roe_V; rw [Finset.mul_sum]
  have hmaster' : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → roe_lhs d c' u ≤ δ ^ (u / (2 - u)) * roe_W d c' := by
    intro u hu0 hu1
    have h := Hmaster u hu0 hu1
    rw [hWeq]
    calc roe_lhs d c' u
        = ∑ i : ι, 4 * (d i : ℝ) * (1 - u) ^ (d i - 1) * c i := by
          unfold roe_lhs; apply Finset.sum_congr rfl; intro i _; rw [hc']; ring
      _ ≤ δ ^ (u / (2 - u)) * (∑ i : ι, 4 * (d i : ℝ) * c i) := h
  have hgain := roe_logGain hc'nn hδ hmaster'
  rw [hVeq, hWeq] at hgain
  
  linarith [hgain]

end StatMech.Probability
