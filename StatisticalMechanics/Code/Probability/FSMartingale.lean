/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Code.Probability.EntropySubadd
import Code.Probability.FSPerEdge

open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







noncomputable def fsm2_dampWeight (p ρ : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
    (ρ ^ (S.erase e).card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S
      / ptn_sigma p) ^ 2


theorem fsm2_dampWeight_nonneg (p ρ : ℝ) (φ : ConfigSpace ι → Bool) (e : ι) :
    0 ≤ fsm2_dampWeight p ρ φ e := by
  unfold fsm2_dampWeight
  exact Finset.sum_nonneg (fun S _ => by positivity)



theorem fsm2_dampWeight_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) (e : ι) :
    fsm2_dampWeight p 1 φ e
      = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
  rw [ptn_infl_eq_fourierWeight hp0 hp1]
  unfold fsm2_dampWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [one_pow, one_pow, one_mul, div_pow, one_div, ← div_eq_inv_mul]




theorem fsm2_dampWeight_le_hc {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (φ : ConfigSpace ι → Bool) (e : ι) :
    fsm2_dampWeight p ρ φ e
      ≤ (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) ^ (2 / q) :=
  ptn_perCoord_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ e



theorem fsm2_dampWeight_le_infl {p ρ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (φ : ConfigSpace ι → Bool) (e : ι) :
    fsm2_dampWeight p ρ φ e
      ≤ OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
  rw [← fsm2_dampWeight_one hp0 hp1 φ e]
  unfold fsm2_dampWeight
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [one_pow]
  have hpow : ρ ^ (S.erase e).card ≤ 1 := pow_le_one₀ h0 h1
  have hpow0 : 0 ≤ ρ ^ (S.erase e).card := by positivity
  nlinarith [hpow, hpow0]



theorem fsm2_dampWeight_pos {p ρ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hρ : 0 < ρ)
    (φ : ConfigSpace ι → Bool) (e : ι)
    (hIe : 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) :
    0 < fsm2_dampWeight p ρ φ e := by
  
  rw [ptn_infl_eq_fourierWeight hp0 hp1] at hIe
  have hσ2pos : 0 < (ptn_sigma p) ^ 2 := pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hsumpos : 0 < ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
      (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
    by_contra h
    push_neg at h
    have hle0 : (1 / (ptn_sigma p) ^ 2) * ∑ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith [hIe]
  
  unfold fsm2_dampWeight
  
  have hwit : ∃ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
      0 < (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by
    by_contra h
    push_neg at h
    have hall : ∀ S ∈ univ.filter (fun S : Finset ι => e ∈ S),
        (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 = 0 := by
      intro S hS
      have hle := h S hS
      have hnn : (0:ℝ) ≤ (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2 := by positivity
      linarith
    rw [Finset.sum_eq_zero hall] at hsumpos
    exact (lt_irrefl 0) hsumpos
  obtain ⟨S, hS, hSpos⟩ := hwit
  apply Finset.sum_pos'
  · intro S' _; positivity
  · refine ⟨S, hS, ?_⟩
    have hfac : 0 < (ρ ^ (S.erase e).card) ^ 2 := by positivity
    have hcoeff : 0 < (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S / ptn_sigma p) ^ 2 := by
      rw [div_pow]
      apply div_pos
      · exact lt_of_le_of_ne (by positivity) (fun hz => by
          rw [← hz] at hSpos; exact (lt_irrefl (0:ℝ)) hSpos)
      · exact hσ2pos
    positivity
















theorem fsm2_logSum_gain {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hρ : 0 < ρ) (_h1 : ρ ≤ 1)
    (_hq1 : 1 ≤ q) (_hq2 : q ≤ 2) (_hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p))
    (φ : ConfigSpace ι → Bool)
    (hpos : 0 < ∑ e ∈ univ.filter (fun e : ι =>
        0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
      OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) :
    (∑ e ∈ univ.filter (fun e : ι =>
        0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
      OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e)
        * Real.log ((∑ e ∈ univ.filter (fun e : ι =>
            0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
          OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e)
          / (∑ e ∈ univ.filter (fun e : ι =>
              0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
            fsm2_dampWeight p ρ φ e))
      ≤ ∑ e ∈ univ.filter (fun e : ι =>
          0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
        OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e
          * Real.log (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e
              / fsm2_dampWeight p ρ φ e) := by
  set t := univ.filter (fun e : ι =>
    0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) with ht
  apply esd_logSum t
    (fun e => OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e)
    (fun e => fsm2_dampWeight p ρ φ e)
  · intro e he
    exact (kkl_infl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _ e)
  · intro e he
    rw [ht, Finset.mem_filter] at he
    exact fsm2_dampWeight_pos hp0 hp1 hρ φ e he.2
  · exact hpos



theorem fsm2_supp_totalInfl {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool) :
    (∑ e ∈ univ.filter (fun e : ι =>
        0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
      OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e)
      = totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  unfold totalInfl
  rw [← Finset.sum_filter_add_sum_filter_not univ
    (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e)
    (fun e => OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e)]
  have hzero : (∑ e ∈ univ.filter (fun e : ι =>
        ¬ 0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
      OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [Finset.mem_filter] at he
    have hnn := kkl_infl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le)
      (fun ω => if φ ω then (1 : ℝ) else 0) e
    linarith [he.2]
  rw [hzero, add_zero]






theorem fsm2_dampSupp_cap [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) (φ : ConfigSpace ι → Bool) :
    (∑ e ∈ univ.filter (fun e : ι =>
        0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
      fsm2_dampWeight p ρ φ e)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q - 1)
          * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  refine le_trans ?_ (ptn_cap_sum hp0 hp1 hq1 hq2 φ)
  
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun e _ _ => fsm2_dampWeight_nonneg p ρ φ e)) ?_
  
  apply Finset.sum_le_sum
  intro e _
  exact fsm2_dampWeight_le_hc hp0 hp1 h0 h1 hq1 hq2 hρsq φ e













theorem fsm2_logGain_capped [Nonempty ι] {p ρ q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hρ : 0 < ρ) (h1 : ρ ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hρsq : ρ ^ 2 = (q - 1) * 4 * p * (1 - p)) (φ : ConfigSpace ι → Bool)
    (hTpos : 0 < totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (_hδ1 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) < 1) :
    totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * (2 / q - 1)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ ∑ e ∈ univ.filter (fun e : ι =>
          0 < OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e),
        OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e
          * Real.log (OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e
              / fsm2_dampWeight p ρ φ e) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  set t := univ.filter (fun e : ι => 0 < OSSS.infl (OSSS.bernoulliWeight p) f e) with htdef
  set Tt := ∑ e ∈ t, OSSS.infl (OSSS.bernoulliWeight p) f e with hTt
  set D := ∑ e ∈ t, fsm2_dampWeight p ρ φ e with hD
  
  have hTtT : Tt = T := fsm2_supp_totalInfl hp0 hp1 φ
  have hTtpos : 0 < Tt := by rw [hTtT]; exact hTpos
  
  have hθ1 : (1:ℝ) ≤ 2 / q := by rw [le_div_iff₀ (by linarith)]; linarith
  have hDcap : D ≤ δ ^ (2 / q - 1) * T :=
    fsm2_dampSupp_cap hp0 hp1 hρ.le h1 hq1 hq2 hρsq φ
  
  have hDpos : 0 < D := by
    rw [hD]
    obtain ⟨e, he⟩ : ∃ e, e ∈ t := by
      by_contra h
      push_neg at h
      have : Tt = 0 := Finset.sum_eq_zero (fun e he => absurd he (h e))
      linarith [hTtpos, this]
    rw [htdef, Finset.mem_filter] at he
    apply Finset.sum_pos'
    · intro e' _; exact fsm2_dampWeight_nonneg p ρ φ e'
    · exact ⟨e, by rw [htdef, Finset.mem_filter]; exact ⟨Finset.mem_univ e, he.2⟩,
        fsm2_dampWeight_pos hp0 hp1 hρ φ e he.2⟩
  
  have hgain := fsm2_logSum_gain hp0 hp1 hρ h1 hq1 hq2 hρsq φ hTtpos
  
  
  have hδpow : 0 < δ ^ (2 / q - 1) := Real.rpow_pos_of_pos hδ0 _
  have hlogbound : T * (2 / q - 1) * Real.log (1 / δ)
      ≤ Tt * Real.log (Tt / D) := by
    rw [hTtT]
    
    have hmono : Real.log (T / (δ ^ (2 / q - 1) * T)) ≤ Real.log (T / D) := by
      apply Real.log_le_log (by positivity)
      apply div_le_div_of_nonneg_left hTpos.le hDpos hDcap
    have hsimp : Real.log (T / (δ ^ (2 / q - 1) * T)) = (2 / q - 1) * Real.log (1 / δ) := by
      rw [show T / (δ ^ (2 / q - 1) * T) = 1 / δ ^ (2 / q - 1) by field_simp]
      rw [show (1:ℝ) / δ ^ (2 / q - 1) = (1 / δ) ^ (2 / q - 1) by
        rw [Real.div_rpow (by norm_num) hδ0.le, Real.one_rpow]]
      rw [Real.log_rpow (by positivity)]
    rw [hsimp] at hmono
    have hTnn : 0 ≤ T := hTpos.le
    calc T * (2 / q - 1) * Real.log (1 / δ)
        = T * ((2 / q - 1) * Real.log (1 / δ)) := by ring
      _ ≤ T * Real.log (T / D) := by exact mul_le_mul_of_nonneg_left hmono hTnn
  
  calc T * (2 / q - 1) * Real.log (1 / δ)
      ≤ Tt * Real.log (Tt / D) := hlogbound
    _ ≤ ∑ e ∈ t, OSSS.infl (OSSS.bernoulliWeight p) f e
          * Real.log (OSSS.infl (OSSS.bernoulliWeight p) f e / fsm2_dampWeight p ρ φ e) := hgain


























theorem fsm2_dampWeight_half_one (φ : ConfigSpace ι → Bool) (e : ι) :
    fsm2_dampWeight (1 / 2 : ℝ) 1 φ e
      = OSSS.infl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) e :=
  fsm2_dampWeight_one (by norm_num) (by norm_num) φ e















def fsm2_residue_statement (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      2 * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
        ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)





theorem fsm2_rhoOptimise_of_residue {q : ℝ} (H : fsm2_residue_statement q) :
    ptn_RhoOptimise q := by
  intro p hp hp1 E _ _ _ φ _Hcap
  exact H p hp hp1 φ





theorem fsm2_residue_c0 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    (0 : ℝ) * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  rw [zero_mul, zero_mul]
  exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _

end StatMech.Probability
