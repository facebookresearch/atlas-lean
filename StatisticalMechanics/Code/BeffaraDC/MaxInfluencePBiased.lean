/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























import Code.BeffaraDC.MaxInfluenceHalf
import Code.Probability.NearHalfBKKKL
import Code.Probability.PBiasedKKLClose

open scoped BigOperators
open Finset Real Set

namespace StatMech.BeffaraDC

open StatMech ConfigSpace Probability OSSS TwoDim

variable {E : Type*} [Fintype E] [DecidableEq E]







theorem maxInfl_ge_scaled_var_mul_log_card_of_logGain [Nonempty E]
    {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 ≤ c) (hc2 : c ≤ 2)
    (φ : ConfigSpace E → Bool)
    (hgain : c * OSSS.var (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / Probability.maxInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ Probability.totalInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)) :
    (c / 2) * OSSS.var (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
      ≤ Probability.maxInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) := by
  let f : ConfigSpace E → ℝ := fun ω => if φ ω then 1 else 0
  let n : ℝ := Fintype.card E
  let V : ℝ := OSSS.var (OSSS.bernoulliWeight p) f
  let δ : ℝ := Probability.maxInfl (OSSS.bernoulliWeight p) f
  change (c / 2) * V * Real.log n / n ≤ δ
  have hcard : 0 < Fintype.card E := Fintype.card_pos
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn0 : 0 ≤ n := hn.le
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hs0 : 0 ≤ Real.sqrt n := hs.le
  have hs_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn0
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact Probability.kkl_var_nonneg hprob f
  have hV4 : V ≤ 1 / 4 := by
    dsimp [V, f]
    exact Probability.kkl_var_le_quarter _ φ
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact Probability.kkl_maxInfl_nonneg hprob f
  have hlog0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    dsimp [n]
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 hcard.ne')
  have hlog_upper : Real.log n ≤ 2 * Real.sqrt n := by
    have h := Real.log_natCast_le_rpow_div (Fintype.card E)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h ⊢
    simpa [n, mul_comm] using h
  have hKKL : c * V * Real.log (1 / δ) ≤ n * δ := by
    have havg : Probability.totalInfl (OSSS.bernoulliWeight p) f ≤ n * δ := by
      simpa [n, δ] using Probability.kkl_maxInfl_ge_avg
        (OSSS.bernoulliWeight p) f
    have hg : c * V * Real.log (1 / δ) ≤
        Probability.totalInfl (OSSS.bernoulliWeight p) f := by
      simpa [V, δ, f] using hgain
    exact hg.trans havg
  by_cases hlarge : 1 / Real.sqrt n ≤ δ
  · have hcdiv : c / 2 ≤ 1 := by linarith
    have hscaled : (c / 2) * V * Real.log n ≤ V * Real.log n := by
      have hVL0 : 0 ≤ V * Real.log n := mul_nonneg hV0 hlog0
      calc
        (c / 2) * V * Real.log n = (c / 2) * (V * Real.log n) := by ring
        _ ≤ 1 * (V * Real.log n) :=
          mul_le_mul_of_nonneg_right hcdiv hVL0
        _ = V * Real.log n := one_mul _
    have hVL : V * Real.log n ≤ (1 / 4 : ℝ) * (2 * Real.sqrt n) :=
      mul_le_mul hV4 hlog_upper hlog0 (by norm_num)
    have hscale_eq : ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n
        = 1 / (2 * Real.sqrt n) := by
      field_simp [hn.ne', hs.ne']
      nlinarith [hs_sq]
    have hscale : ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n
        ≤ 1 / Real.sqrt n := by
      rw [hscale_eq]
      field_simp [hs.ne']
      nlinarith [hs]
    calc
      (c / 2) * V * Real.log n / n ≤ (V * Real.log n) / n :=
        div_le_div_of_nonneg_right hscaled hn0
      _ ≤ ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n :=
        div_le_div_of_nonneg_right hVL hn0
      _ ≤ 1 / Real.sqrt n := hscale
      _ ≤ δ := hlarge
  · have hsmall : δ < 1 / Real.sqrt n := lt_of_not_ge hlarge
    rcases hδ0.eq_or_lt with hδ | hδ
    · have hδz : δ = 0 := hδ.symm
      have htotal : Probability.totalInfl (OSSS.bernoulliWeight p) f ≤ n * δ := by
        simpa [n, δ] using Probability.kkl_maxInfl_ge_avg
          (OSSS.bernoulliWeight p) f
      have hpoincare : V ≤ Probability.totalInfl (OSSS.bernoulliWeight p) f := by
        dsimp [V]
        exact Probability.kkl_var_le_total_influence hprob φ
      have hV : V = 0 := by
        have : V ≤ 0 := by simpa [hδz] using hpoincare.trans htotal
        exact le_antisymm this hV0
      simp [hV, hδz]
    · have hs_le_inv : Real.sqrt n ≤ 1 / δ := by
        rw [le_div_iff₀ hδ]
        have hmul := (lt_div_iff₀ hs).mp hsmall
        simpa [mul_comm] using hmul.le
      have hlog_lower : Real.log n / 2 ≤ Real.log (1 / δ) := by
        rw [← Real.log_sqrt hn0]
        exact Real.log_le_log hs hs_le_inv
      have hVlog : (c / 2) * V * Real.log n
          ≤ c * V * Real.log (1 / δ) := by
        have hmul := mul_le_mul_of_nonneg_left hlog_lower (mul_nonneg hc0 hV0)
        nlinarith
      have hmain : (c / 2) * V * Real.log n ≤ n * δ := hVlog.trans hKKL
      exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using hmain)




noncomputable def pBiasedCorrection (p : ℝ) : ℝ :=
  (1 - 4 * p * (1 - p)) * (Probability.ptn_sigma p) ^ 2


theorem pBiasedCorrection_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ pBiasedCorrection p := by
  rw [pBiasedCorrection, Probability.ptn_sigma_sq hp0 hp1]
  exact mul_nonneg (by nlinarith [sq_nonneg (1 - 2 * p)]) (by nlinarith)



theorem pBiasedCorrection_le_one_sixteenth {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    pBiasedCorrection p ≤ 1 / 16 := by
  rw [pBiasedCorrection, Probability.ptn_sigma_sq hp0 hp1]
  nlinarith [sq_nonneg (p * (1 - p) - 1 / 8)]










theorem maxInfl_pbiased_corrected [Nonempty E]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace E → Bool) :
    OSSS.var (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
        / (1 + pBiasedCorrection p * Real.log (Fintype.card E : ℝ))
      ≤ Probability.maxInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) := by
  let f : ConfigSpace E → ℝ := fun ω => if φ ω then 1 else 0
  let n : ℝ := Fintype.card E
  let V : ℝ := OSSS.var (OSSS.bernoulliWeight p) f
  let δ : ℝ := Probability.maxInfl (OSSS.bernoulliWeight p) f
  let L : ℝ := Real.log (1 / δ)
  let a : ℝ := pBiasedCorrection p
  change V * Real.log n / n / (1 + a * Real.log n) ≤ δ
  have hcard : 0 < Fintype.card E := Fintype.card_pos
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn0 : 0 ≤ n := hn.le
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hs0 : 0 ≤ Real.sqrt n := hs.le
  have hs_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn0
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact Probability.kkl_var_nonneg hprob f
  have hV4 : V ≤ 1 / 4 := by
    dsimp [V, f]
    exact Probability.kkl_var_le_quarter _ φ
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact Probability.kkl_maxInfl_nonneg hprob f
  have hδ1 : δ ≤ 1 := by
    dsimp [δ, f]
    exact Probability.cvg_maxInfl_le_one hp0.le hp1.le φ
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact pBiasedCorrection_nonneg hp0 hp1
  have hlog0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    dsimp [n]
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 hcard.ne')
  have hden1 : 1 ≤ 1 + a * Real.log n :=
    le_add_of_nonneg_right (mul_nonneg ha0 hlog0)
  have hdenpos : 0 < 1 + a * Real.log n := lt_of_lt_of_le zero_lt_one hden1
  have hL0 : 0 ≤ L := by
    by_cases hz : δ = 0
    · simp [L, hz]
    · have hpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hz)
      dsimp [L]
      exact Real.log_nonneg ((one_le_div hpos).2 hδ1)
  have hfactor0 : 0 ≤ 1 + 2 * a * L := by
    nlinarith [mul_nonneg ha0 hL0]
  have hnear : 2 * V * L ≤
      (1 + 2 * a * L) * Probability.totalInfl (OSSS.bernoulliWeight p) f := by
    have h := Probability.nhb_nearHalf_kkl hp0 hp1 φ
    simpa only [V, δ, L, a, pBiasedCorrection, f, mul_assoc] using h
  have havg : Probability.totalInfl (OSSS.bernoulliWeight p) f ≤ n * δ := by
    simpa [n, δ] using Probability.kkl_maxInfl_ge_avg
      (OSSS.bernoulliWeight p) f
  have hnear' : 2 * V * L ≤ (1 + 2 * a * L) * (n * δ) :=
    hnear.trans (mul_le_mul_of_nonneg_left havg hfactor0)
  have hlog_upper : Real.log n ≤ 2 * Real.sqrt n := by
    have h := Real.log_natCast_le_rpow_div (Fintype.card E)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h ⊢
    simpa [n, mul_comm] using h
  by_cases hlarge : 1 / Real.sqrt n ≤ δ
  · have hnum0 : 0 ≤ V * Real.log n / n :=
      div_nonneg (mul_nonneg hV0 hlog0) hn0
    have hdivide : V * Real.log n / n / (1 + a * Real.log n)
        ≤ V * Real.log n / n := by
      exact (div_le_iff₀ hdenpos).2 (by
        have := mul_le_mul_of_nonneg_left hden1 hnum0
        nlinarith)
    have hVL : V * Real.log n ≤ (1 / 4 : ℝ) * (2 * Real.sqrt n) :=
      mul_le_mul hV4 hlog_upper hlog0 (by norm_num)
    have hscale_eq : ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n
        = 1 / (2 * Real.sqrt n) := by
      field_simp [hn.ne', hs.ne']
      nlinarith [hs_sq]
    have hscale : ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n
        ≤ 1 / Real.sqrt n := by
      rw [hscale_eq]
      field_simp [hs.ne']
      nlinarith [hs]
    calc
      V * Real.log n / n / (1 + a * Real.log n) ≤ V * Real.log n / n := hdivide
      _ ≤ ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n :=
        div_le_div_of_nonneg_right hVL hn0
      _ ≤ 1 / Real.sqrt n := hscale
      _ ≤ δ := hlarge
  · have hsmall : δ < 1 / Real.sqrt n := lt_of_not_ge hlarge
    rcases hδ0.eq_or_lt with hδ | hδ
    · have hδz : δ = 0 := hδ.symm
      have htotal : Probability.totalInfl (OSSS.bernoulliWeight p) f ≤ n * δ := havg
      have hpoincare : V ≤ Probability.totalInfl (OSSS.bernoulliWeight p) f := by
        dsimp [V]
        exact Probability.kkl_var_le_total_influence hprob φ
      have hV : V = 0 := by
        have : V ≤ 0 := by simpa [hδz] using hpoincare.trans htotal
        exact le_antisymm this hV0
      simp [hV, hδz]
    · have hs_le_inv : Real.sqrt n ≤ 1 / δ := by
        rw [le_div_iff₀ hδ]
        have hmul := (lt_div_iff₀ hs).mp hsmall
        simpa [mul_comm] using hmul.le
      have hlog_lower : Real.log n / 2 ≤ L := by
        dsimp [L]
        rw [← Real.log_sqrt hn0]
        exact Real.log_le_log hs hs_le_inv
      have hCpos : 0 < 1 + 2 * a * L := by positivity
      have hratio : Real.log n / (1 + a * Real.log n)
          ≤ (2 * L) / (1 + 2 * a * L) := by
        apply (div_le_div_iff₀ hdenpos hCpos).2
        have hg : Real.log n ≤ 2 * L := by linarith
        nlinarith [hg]
      have hratioV : V * (Real.log n / (1 + a * Real.log n))
          ≤ V * ((2 * L) / (1 + 2 * a * L)) :=
        mul_le_mul_of_nonneg_left hratio hV0
      have hnearDiv : 2 * V * L / (1 + 2 * a * L) ≤ n * δ := by
        apply (div_le_iff₀ hCpos).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hnear'
      have hmain : V * Real.log n / (1 + a * Real.log n) ≤ n * δ := by
        calc
          V * Real.log n / (1 + a * Real.log n)
              = V * (Real.log n / (1 + a * Real.log n)) := by ring
          _ ≤ V * ((2 * L) / (1 + 2 * a * L)) := hratioV
          _ = 2 * V * L / (1 + 2 * a * L) := by ring
          _ ≤ n * δ := hnearDiv
      calc
        V * Real.log n / n / (1 + a * Real.log n)
            = (V * Real.log n / (1 + a * Real.log n)) / n := by ring
        _ ≤ (n * δ) / n := div_le_div_of_nonneg_right hmain hn0
        _ = δ := by field_simp [hn.ne']





theorem maxInfluence_pbiased_corrected [Nonempty E]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (A : Set (ConfigSpace E)) :
    ∃ e : E,
      StatMech.prob p A * (1 - StatMech.prob p A)
          * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
          / (1 + pBiasedCorrection p * Real.log (Fintype.card E : ℝ))
        ≤ influence p A e := by
  classical
  let φ : ConfigSpace E → Bool := fun ω => decide (ω ∈ A)
  have hmax := maxInfl_pbiased_corrected (E := E) hp0 hp1 φ
  rw [TwoDim.kklw_decide_eq_indicator A, TwoDim.kklw_var_eq] at hmax
  obtain ⟨e, he⟩ := Probability.kkl_exists_maxInfl
    (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ)))
  refine ⟨e, ?_⟩
  rw [TwoDim.kklw_influence_eq_infl, he]
  exact hmax




theorem maxInfluence_qOne_compactWindow [Nonempty E]
    {ε p : ℝ} (hε0 : 0 < ε) (hp : p ∈ Set.Icc ε (1 - ε))
    (A : Set (ConfigSpace E)) :
    ∃ e : E,
      StatMech.prob p A * (1 - StatMech.prob p A)
          * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
          / (1 + pBiasedCorrection p * Real.log (Fintype.card E : ℝ))
        ≤ influence p A e := by
  have hp0 : 0 < p := lt_of_lt_of_le hε0 hp.1
  have hp1 : p < 1 := by linarith [hp.2, hε0]
  exact maxInfluence_pbiased_corrected hp0 hp1 A





theorem maxInfluence_pbiased_of_absorbed [Nonempty E]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (A : Set (ConfigSpace E))
    (hcorr : 2 * (1 - 4 * p * (1 - p)) * (Probability.ptn_sigma p) ^ 2
        * Real.log (1 / Probability.maxInfl (OSSS.bernoulliWeight p)
          (A.indicator (fun _ => (1 : ℝ)))) ≤ 1) :
    ∃ e : E,
      (1 / 2 : ℝ) * (StatMech.prob p A * (1 - StatMech.prob p A))
          * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
        ≤ influence p A e := by
  classical
  let φ : ConfigSpace E → Bool := fun ω => decide (ω ∈ A)
  have hgain := Probability.nhb_nearHalf_kkl_absorbed hp0 hp1 φ (by
    simpa [φ, TwoDim.kklw_decide_eq_indicator A] using hcorr)
  have hmax := maxInfl_ge_scaled_var_mul_log_card_of_logGain
    (E := E) hp0 hp1 (c := 1) (by norm_num) (by norm_num) φ (by
      simpa using hgain)
  rw [TwoDim.kklw_decide_eq_indicator A, TwoDim.kklw_var_eq] at hmax
  obtain ⟨e, he⟩ := Probability.kkl_exists_maxInfl
    (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ)))
  refine ⟨e, ?_⟩
  rw [TwoDim.kklw_influence_eq_infl, he]
  simpa using hmax



theorem maxInfluence_pbiased_largeInfl
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (A : Set (ConfigSpace E))
    (hlarge : Real.exp (-(1 / (2 * (p * (1 - p)))))
      ≤ Probability.maxInfl (OSSS.bernoulliWeight p)
          (A.indicator (fun _ => (1 : ℝ)))) :
    ∃ e : E,
      StatMech.prob p A * (1 - StatMech.prob p A)
          * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
        ≤ influence p A e := by
  classical
  let φ : ConfigSpace E → Bool := fun ω => decide (ω ∈ A)
  have hgain := Probability.pkc_kkl_logGain_largeInfl hp0 hp1 φ (by
    simpa [φ, TwoDim.kklw_decide_eq_indicator A] using hlarge)
  have hmax := maxInfl_ge_scaled_var_mul_log_card_of_logGain
    (E := E) hp0 hp1 (c := 2) (by norm_num) (by norm_num) φ hgain
  rw [TwoDim.kklw_decide_eq_indicator A, TwoDim.kklw_var_eq] at hmax
  obtain ⟨e, he⟩ := Probability.kkl_exists_maxInfl
    (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ)))
  refine ⟨e, ?_⟩
  rw [TwoDim.kklw_influence_eq_infl, he]
  simpa using hmax




theorem maxInfluence_pbiased_of_hypercontractive
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (H : Probability.KKLHypercontractive p 2) (A : Set (ConfigSpace E)) :
    ∃ e : E,
      StatMech.prob p A * (1 - StatMech.prob p A)
          * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
        ≤ influence p A e := by
  classical
  let φ : ConfigSpace E → Bool := fun ω => decide (ω ∈ A)
  have hgain : 2 * OSSS.var (OSSS.bernoulliWeight p)
        (fun ω => if φ ω then (1 : ℝ) else 0)
      * Real.log (1 / Probability.maxInfl (OSSS.bernoulliWeight p)
        (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ Probability.totalInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) := H φ
  have hmax := maxInfl_ge_scaled_var_mul_log_card_of_logGain
    (E := E) hp0 hp1 (c := 2) (by norm_num) (by norm_num) φ hgain
  rw [TwoDim.kklw_decide_eq_indicator A, TwoDim.kklw_var_eq] at hmax
  obtain ⟨e, he⟩ := Probability.kkl_exists_maxInfl
    (OSSS.bernoulliWeight p) (A.indicator (fun _ => (1 : ℝ)))
  refine ⟨e, ?_⟩
  rw [TwoDim.kklw_influence_eq_infl, he]
  simpa using hmax










theorem maxInfluence_qOne_compactWindow_of_bkkkl
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    {ε p : ℝ} (hε0 : 0 < ε) (hp : p ∈ Set.Icc ε (1 - ε))
    (Hpb : Probability.kpb_PBiasedHC (1 - ε / 2))
    (A : Set (ConfigSpace E)) :
    ∃ e : E,
      StatMech.prob p A * (1 - StatMech.prob p A)
          * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
        ≤ influence p A e := by
  have hp0 : 0 < p := lt_of_lt_of_le hε0 hp.1
  have hp1 : p < 1 := by linarith [hp.2, hε0]
  have H : Probability.KKLHypercontractive p 2 := by
    intro E' _ _ _ φ
    rcases lt_trichotomy p (1 / 2 : ℝ) with hbelow | hmid | habove
    · have href : Probability.KKLHypercontractive (1 - p) 2 := by
        apply Hpb (1 - p)
        constructor
        · linarith
        · linarith [hp.1]
      have hreflected : Probability.KKLHypercontractive (1 - (1 - p)) 2 :=
        Probability.kpb_kkl_reflect (p := 1 - p) href
      have hr := hreflected (E := E') φ
      simpa only [sub_sub_cancel] using hr
    · subst p
      exact Probability.kpb_PBiasedHC_half_holds (E := E') φ
    · have hpwindow : p ∈ Set.Ioo (1 / 2 : ℝ) (1 - ε / 2) := by
        constructor
        · exact habove
        · linarith [hp.2]
      exact Hpb p hpwindow φ
  exact maxInfluence_pbiased_of_hypercontractive hp0 hp1 H A

end StatMech.BeffaraDC
