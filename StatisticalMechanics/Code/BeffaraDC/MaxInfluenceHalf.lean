/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















import Code.Probability.VarGapProve2
import Code.TwoDim.KKLWire

open scoped BigOperators
open Finset Real Set

namespace StatMech.BeffaraDC

open StatMech ConfigSpace Probability OSSS TwoDim

variable {E : Type*} [Fintype E] [DecidableEq E]











theorem maxInfl_half_ge_var_mul_log_card_div_card [Nonempty E]
    (φ : ConfigSpace E → Bool) :
    OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
      ≤ Probability.maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
          (fun ω => if φ ω then (1 : ℝ) else 0) := by
  let f : ConfigSpace E → ℝ := fun ω => if φ ω then 1 else 0
  let n : ℝ := Fintype.card E
  let V : ℝ := OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) f
  let δ : ℝ := Probability.maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f
  change V * Real.log n / n ≤ δ
  have hcard : 0 < Fintype.card E := Fintype.card_pos
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn0 : 0 ≤ n := hn.le
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hs0 : 0 ≤ Real.sqrt n := hs.le
  have hs_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn0
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact Probability.kkl_var_nonneg
      (OSSS.bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) f
  have hV4 : V ≤ 1 / 4 := by
    dsimp [V, f]
    exact Probability.kkl_var_le_quarter _ φ
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact Probability.kkl_maxInfl_nonneg
      (OSSS.bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) f
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
  have hKKL : 2 * V * Real.log (1 / δ) ≤ n * δ := by
    have htotal : 2 * V * Real.log (1 / δ)
        ≤ Probability.totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f := by
      have h := Probability.vgp2_kkl_logGain_half φ
      rw [← Probability.kkl_var_indicator_eq] at h
      simpa [V, δ, f] using h
    have havg : Probability.totalInfl
        (OSSS.bernoulliWeight (1 / 2 : ℝ)) f ≤ n * δ := by
      simpa [n, δ] using
        (Probability.kkl_maxInfl_ge_avg
          (OSSS.bernoulliWeight (1 / 2 : ℝ)) f)
    exact htotal.trans havg
  by_cases hlarge : 1 / Real.sqrt n ≤ δ
  · have hVL : V * Real.log n ≤ (1 / 4 : ℝ) * (2 * Real.sqrt n) :=
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
      V * Real.log n / n
          ≤ ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n :=
            div_le_div_of_nonneg_right hVL hn0
      _ ≤ 1 / Real.sqrt n := hscale
      _ ≤ δ := hlarge
  · have hsmall : δ < 1 / Real.sqrt n := lt_of_not_ge hlarge
    rcases hδ0.eq_or_lt with hδ | hδ
    · have hδz : δ = 0 := hδ.symm
      have htotal : Probability.totalInfl
          (OSSS.bernoulliWeight (1 / 2 : ℝ)) f ≤ n * δ := by
        simpa [n, δ] using
          (Probability.kkl_maxInfl_ge_avg
            (OSSS.bernoulliWeight (1 / 2 : ℝ)) f)
      have hpoincare : V ≤ Probability.totalInfl
          (OSSS.bernoulliWeight (1 / 2 : ℝ)) f := by
        dsimp [V]
        exact Probability.kkl_var_le_total_influence
          (OSSS.bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) φ
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
      have hVlog : V * Real.log n ≤ 2 * V * Real.log (1 / δ) := by
        have := mul_le_mul_of_nonneg_left hlog_lower hV0
        nlinarith
      have hmain : V * Real.log n ≤ n * δ := hVlog.trans hKKL
      exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using hmain)











theorem maxInfluence_half [Nonempty E]
    (A : Set (ConfigSpace E)) :
    ∃ e : E,
      StatMech.prob (1 / 2 : ℝ) A * (1 - StatMech.prob (1 / 2 : ℝ) A)
          * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
        ≤ influence (1 / 2 : ℝ) A e := by
  classical
  let φ : ConfigSpace E → Bool := fun ω => decide (ω ∈ A)
  have hmax := maxInfl_half_ge_var_mul_log_card_div_card (E := E) φ
  rw [TwoDim.kklw_decide_eq_indicator A, TwoDim.kklw_var_eq] at hmax
  obtain ⟨e, he⟩ := Probability.kkl_exists_maxInfl
    (OSSS.bernoulliWeight (1 / 2 : ℝ)) (A.indicator (fun _ => (1 : ℝ)))
  refine ⟨e, ?_⟩
  rw [TwoDim.kklw_influence_eq_infl, he]
  exact hmax




theorem exists_influence_pos_half_of_nontrivial [Nonempty E]
    (A : Set (ConfigSpace E)) (hcard : 2 ≤ Fintype.card E)
    (hprob0 : 0 < StatMech.prob (1 / 2 : ℝ) A)
    (hprob1 : StatMech.prob (1 / 2 : ℝ) A < 1) :
    ∃ e : E, 0 < influence (1 / 2 : ℝ) A e := by
  obtain ⟨e, he⟩ := maxInfluence_half A
  refine ⟨e, lt_of_lt_of_le ?_ he⟩
  have hcard1 : (1 : ℝ) < Fintype.card E := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hcard)
  have hcard0 : (0 : ℝ) < Fintype.card E := by linarith
  have hvar : 0 < StatMech.prob (1 / 2 : ℝ) A
      * (1 - StatMech.prob (1 / 2 : ℝ) A) :=
    mul_pos hprob0 (sub_pos.mpr hprob1)
  exact div_pos (mul_pos hvar (Real.log_pos hcard1)) hcard0



theorem maxInfluence_half_of_increasing [Nonempty E]
    (A : Set (ConfigSpace E)) (_hA : IsIncreasing A) :
    ∃ e : E,
      StatMech.prob (1 / 2 : ℝ) A * (1 - StatMech.prob (1 / 2 : ℝ) A)
          * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
        ≤ influence (1 / 2 : ℝ) A e :=
  maxInfluence_half A

end StatMech.BeffaraDC
