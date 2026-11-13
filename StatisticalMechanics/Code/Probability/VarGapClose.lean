/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.Probability.BKKKLLevel2Prove

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





theorem vgc_totalInfl_zero_of_maxInfl_zero [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hδ0 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
    totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0 := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  unfold totalInfl
  apply Finset.sum_eq_zero
  intro e _
  have hle : OSSS.infl (OSSS.bernoulliWeight p) f e
      ≤ maxInfl (OSSS.bernoulliWeight p) f := kkl_infl_le_maxInfl _ f e
  have hge : 0 ≤ OSSS.infl (OSSS.bernoulliWeight p) f e :=
    kkl_infl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f e
  rw [hδ0] at hle
  linarith





theorem vgc_var_zero_of_maxInfl_zero [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hδ0 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) = 0 := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  have hpoin := bkt2p_poincare_half hp0 hp1 φ
  rw [← hμ] at hpoin
  have hT0 := vgc_totalInfl_zero_of_maxInfl_zero hp0 hp1 φ hδ0
  rw [hT0, mul_zero] at hpoin
  
  have hvarF := ptn_var_eq_fourierWeight hp0 hp1 f
  have hvar_eq : OSSS.var (OSSS.bernoulliWeight p) f = μ * (1 - μ) := by
    rw [mil_var_eq φ, ← hμ]; ring
  have hvar_nn : 0 ≤ μ * (1 - μ) := by
    rw [← hvar_eq, hvarF]
    exact Finset.sum_nonneg (fun S _ => sq_nonneg _)
  linarith






















def vgc_VarPowerCore (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
      ∀ u : ℝ, 0 < u → u < 1 →
        0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) →
          OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
            ≤ (u / (4 + 2 * u))
              * ((ptn_sigma p) ^ 2
                * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
                    ^ (u / (2 - u))
                  * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))












theorem vgc_varGapCore_of_varPower {q : ℝ} (H : vgc_VarPowerCore q) :
    bkt2p_VarGapCore q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  set f := fun ω : ConfigSpace E => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδdef
  set T := totalInfl (OSSS.bernoulliWeight p) f with hTdef
  set L1 : ℝ := ∑ S ∈ univ.filter (fun S : Finset E => S.card = 1), (ptn_coeff p f S) ^ 2 with hL1
  set σ2 := (ptn_sigma p) ^ 2 with hσ2def
  have hσ2pos : 0 < σ2 := by rw [hσ2def]; exact pow_pos (ptn_sigma_pos hp0 hp1) 2
  have hTnn : 0 ≤ T := by
    rw [hTdef]; exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hδnn : 0 ≤ δ := by
    rw [hδdef]; exact kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  
  have hvar_nn : 0 ≤ μ * (1 - μ) := by
    have hvarF := ptn_var_eq_fourierWeight hp0 hp1 f
    have hvar_eq : OSSS.var (OSSS.bernoulliWeight p) f = μ * (1 - μ) := by
      rw [mil_var_eq φ, ← hμ]; ring
    rw [← hvar_eq, hvarF]
    exact Finset.sum_nonneg (fun S _ => sq_nonneg _)
  
  have hL1le : L1 ≤ μ * (1 - μ) := by
    rw [hL1, hμ]; exact mil_level1_le_var hp0 hp1 φ
  have hL1nn : 0 ≤ L1 := by
    rw [hL1]; exact Finset.sum_nonneg (fun S _ => sq_nonneg _)
  rcases eq_or_lt_of_le hδnn with hδ00 | hδ0
  · 
    have hδ0' : δ = 0 := hδ00.symm
    have hvar0 : μ * (1 - μ) = 0 := by
      have := vgc_var_zero_of_maxInfl_zero hp0 hp1 φ (by rw [← hδdef]; exact hδ0')
      rw [← hμ] at this; exact this
    have hT0 : T = 0 := vgc_totalInfl_zero_of_maxInfl_zero hp0 hp1 φ (by rw [← hδdef]; exact hδ0')
    have hL10 : L1 = 0 := le_antisymm (by rw [hvar0] at hL1le; exact hL1le) hL1nn
    refine ⟨u / 2, by linarith, by linarith, 1, le_refl 1, ?_⟩
    
    rw [hvar0, hT0, hL10]
    simp
  · 
    have hdpow_pos : 0 < δ ^ (u / (2 - u)) := Real.rpow_pos_of_pos hδ0 _
    have h1u : (1 : ℝ) - u < 1 := by linarith
    have h1unn : (0 : ℝ) ≤ 1 - u := by linarith
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
      (x := (1 / 2 : ℝ) * δ ^ (u / (2 - u))) (by positivity) h1u
    refine ⟨u / 2, by linarith, by linarith, k + 1, by omega, ?_⟩
    
    have hmono : (1 - u) ^ (k + 1) ≤ (1 - u) ^ k :=
      pow_le_pow_of_le_one h1unn (by linarith) (by omega)
    have hpowk1 : (1 - u) ^ (k + 1) ≤ (1 / 2 : ℝ) * δ ^ (u / (2 - u)) :=
      le_trans hmono (le_of_lt hk)
    
    have hprice : (4 : ℝ) / (u - u / 2) = 8 / u := by
      rw [show u - u / 2 = u / 2 from by ring]; field_simp; ring
    rw [hprice]
    
    have hVP := H p hp hp1 φ u hu0 hu1 hδ0
    
    set P : ℝ := σ2 * (δ ^ (u / (2 - u)) * T) with hPdef
    have hPnn : 0 ≤ P := by rw [hPdef]; positivity
    
    
    
    
    
    
    have hupos : 0 < u := hu0
    
    have hbudget_lb : 2 * P
        ≤ 4 * σ2 * (δ ^ (u / (2 - u)) - (1 - u) ^ (k + 1)) * T := by
      rw [hPdef]
      have hfac : 4 * σ2 * (δ ^ (u / (2 - u)) - (1 - u) ^ (k + 1)) * T
          = 4 * σ2 * T * (δ ^ (u / (2 - u)) - (1 - u) ^ (k + 1)) := by ring
      rw [hfac]
      have h2P : 2 * (σ2 * (δ ^ (u / (2 - u)) * T))
          = 4 * σ2 * T * ((1 / 2 : ℝ) * δ ^ (u / (2 - u))) := by ring
      rw [h2P]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hpowk1]
    
    
    
    have hkey : (8 / u + 4) * (μ * (1 - μ)) ≤ 2 * P := by
      have hcoef : (0 : ℝ) ≤ 8 / u + 4 := by positivity
      calc (8 / u + 4) * (μ * (1 - μ))
          ≤ (8 / u + 4) * ((u / (4 + 2 * u)) * P) :=
            mul_le_mul_of_nonneg_left hVP hcoef
        _ = 2 * P := by
            have h4u : (4 : ℝ) + 2 * u ≠ 0 := by positivity
            field_simp
            ring
    
    have hstep : (8 / u) * (μ * (1 - μ))
        ≤ 4 * σ2 * (δ ^ (u / (2 - u)) - (1 - u) ^ (k + 1)) * T - 4 * L1 := by
      have hexpand : (8 / u + 4) * (μ * (1 - μ)) = (8 / u) * (μ * (1 - μ)) + 4 * (μ * (1 - μ)) := by
        ring
      have h1 : (8 / u) * (μ * (1 - μ)) + 4 * L1 ≤ 2 * P := by
        calc (8 / u) * (μ * (1 - μ)) + 4 * L1
            ≤ (8 / u) * (μ * (1 - μ)) + 4 * (μ * (1 - μ)) :=
              by linarith [mul_le_mul_of_nonneg_left hL1le (by norm_num : (0:ℝ) ≤ 4)]
          _ = (8 / u + 4) * (μ * (1 - μ)) := by rw [hexpand]
          _ ≤ 2 * P := hkey
      linarith [hbudget_lb]
    
    have hgoal_lhs : (8 / u) * (μ * (1 - μ)) = (8 / u) * (μ * (1 - μ)) := rfl
    
    
    calc (8 / u) * (μ * (1 - μ))
        ≤ 4 * σ2 * (δ ^ (u / (2 - u)) - (1 - u) ^ (k + 1)) * T - 4 * L1 := hstep
      _ = 4 * σ2
            * (δ ^ (u / (2 - u)) - (1 - u) ^ (k + 1))
            * T - 4 * L1 := by ring






theorem vgc_levelGe2_of_varPower {q : ℝ} (H : vgc_VarPowerCore q) :
    bkt2_levelGe2MasterResidue q :=
  bkt2p_levelGe2_of_varGap (vgc_varGapCore_of_varPower H)


theorem vgc_remaining_of_varPower {q : ℝ} (H : vgc_VarPowerCore q) :
    bkt2_RemainingGoal q :=
  bkt2p_remaining_of_varGap (vgc_varGapCore_of_varPower H)


theorem vgc_master_of_varPower {q : ℝ} (H : vgc_VarPowerCore q) :
    pro_PBiasedMaster q :=
  bkt2p_master_of_varGap (vgc_varGapCore_of_varPower H)







theorem vgc_rhoOptimise_of_varPower {q : ℝ} (H : vgc_VarPowerCore q) :
    ptn_RhoOptimise q :=
  bkt2p_rhoOptimise_of_varGap (vgc_varGapCore_of_varPower H)









theorem vgc_varPowerCore_c0 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {u : ℝ} (hu0 : 0 < u) (_hu1 : u < 1) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
      ≤ (u / (4 + 2 * u))
        * ((ptn_sigma p) ^ 2
          * ((maxInfl (OSSS.bernoulliWeight p)
              (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))
              ^ (u / (2 - u))
            * totalInfl (OSSS.bernoulliWeight p)
                (fun ω => if (fun _ => false : ConfigSpace E → Bool) ω then (1 : ℝ) else 0))) := by
  set f0 : ConfigSpace E → Bool := fun _ => false with hf0
  
  have hf0zero : (fun ω => if f0 ω then (1 : ℝ) else 0) = (fun _ : ConfigSpace E => (0 : ℝ)) := by
    funext ω; rw [hf0]; simp
  have hμ0 : OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) = 0 := by
    rw [hf0zero]; unfold OSSS.expect; simp
  rw [hμ0]
  simp only [sub_zero, zero_mul]
  
  have hδnn : 0 ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) :=
    kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
  have hTnn : 0 ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if f0 ω then (1 : ℝ) else 0) :=
    kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
  have h4u : (0 : ℝ) ≤ u / (4 + 2 * u) := by positivity
  positivity









theorem vgc_poincare_is_delta0_instance {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ (ptn_sigma p) ^ 2
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  bkt2p_poincare_half hp0 hp1 φ





theorem vgc_gap_vanishes_at_p_half {u : ℝ} (d : ℕ) :
    (1 - u) ^ (d - 1) - (((1 - u) * (4 * (1/2 : ℝ) * (1 - 1/2))) ^ (d - 1)) = 0 :=
  bkt2p_gap_vanishes_at_p_half d

end StatMech.Probability
