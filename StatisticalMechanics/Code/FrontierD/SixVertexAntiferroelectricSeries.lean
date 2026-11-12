/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierD.SixVertexWidthFreeEnergy
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset Filter Topology

namespace StatMech.FrontierD



noncomputable def sixVertexAntiferroelectricLambda (c : ℝ) : ℝ :=
  Real.arcosh ((c ^ 2 - 2) / 2)

theorem sixVertexAntiferroelectricLambda_pos {c : ℝ} (hc : 2 < c) :
    0 < sixVertexAntiferroelectricLambda c := by
  apply Real.arcosh_pos
  dsimp [sixVertexAntiferroelectricLambda]
  nlinarith

theorem sixVertex_cosh_antiferroelectricLambda {c : ℝ} (hc : 2 < c) :
    Real.cosh (sixVertexAntiferroelectricLambda c) = (c ^ 2 - 2) / 2 := by
  apply Real.cosh_arcosh
  nlinarith


theorem sixVertexAntiferroelectricLambda_unique {c lam : ℝ} (hlam : 0 < lam)
    (hcosh : Real.cosh lam = (c ^ 2 - 2) / 2) :
    lam = sixVertexAntiferroelectricLambda c := by
  rw [sixVertexAntiferroelectricLambda, ← hcosh, Real.arcosh_cosh hlam.le]


noncomputable def sixVertexFreeEnergySeriesTerm (lam : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((n + 1 : ℝ) * lam)) * Real.tanh ((n + 1 : ℝ) * lam) / (n + 1 : ℝ)

private theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq]
  apply div_pos
  · exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  · positivity

theorem sixVertexFreeEnergySeriesTerm_nonneg {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    0 ≤ sixVertexFreeEnergySeriesTerm lam n := by
  unfold sixVertexFreeEnergySeriesTerm
  exact div_nonneg
    (mul_nonneg (Real.exp_nonneg _)
      (tanh_pos_of_pos (mul_pos (by positivity) hlam)).le)
    (by positivity)

theorem sixVertexFreeEnergySeriesTerm_norm_le {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    ‖sixVertexFreeEnergySeriesTerm lam n‖ ≤ Real.exp (-lam) ^ (n + 1) := by
  have htanh : Real.tanh ((n + 1 : ℝ) * lam) ≤ 1 :=
    (Real.tanh_lt_one _).le
  have hden : 1 ≤ (n + 1 : ℝ) := by norm_num
  have hnum : Real.exp (-((n + 1 : ℝ) * lam)) *
      Real.tanh ((n + 1 : ℝ) * lam) ≤ Real.exp (-((n + 1 : ℝ) * lam)) := by
    exact mul_le_of_le_one_right (Real.exp_nonneg _) htanh
  have hterm : sixVertexFreeEnergySeriesTerm lam n ≤
      Real.exp (-((n + 1 : ℝ) * lam)) := by
    rw [sixVertexFreeEnergySeriesTerm, div_le_iff₀ (by positivity)]
    calc
      Real.exp (-((n + 1 : ℝ) * lam)) * Real.tanh ((n + 1 : ℝ) * lam)
          ≤ Real.exp (-((n + 1 : ℝ) * lam)) := hnum
      _ ≤ Real.exp (-((n + 1 : ℝ) * lam)) * (n + 1 : ℝ) :=
        le_mul_of_one_le_right (Real.exp_nonneg _) hden
  rw [Real.norm_eq_abs, abs_of_nonneg (sixVertexFreeEnergySeriesTerm_nonneg hlam n)]
  calc
    sixVertexFreeEnergySeriesTerm lam n
        ≤ Real.exp (-((n + 1 : ℝ) * lam)) := hterm
    _ = Real.exp (-lam) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring



theorem summable_sixVertexFreeEnergySeriesTerm {lam : ℝ} (hlam : 0 < lam) :
    Summable (sixVertexFreeEnergySeriesTerm lam) := by
  have hq0 : 0 ≤ Real.exp (-lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-lam) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => Real.exp (-lam) ^ (n + 1)) :=
    (summable_geometric_of_lt_one hq0 hq1).comp_injective Nat.succ_injective
  exact hgeom.of_norm_bounded (sixVertexFreeEnergySeriesTerm_norm_le hlam)


noncomputable def sixVertexFreeEnergySeries (lam : ℝ) : ℝ :=
  ∑' n : ℕ, sixVertexFreeEnergySeriesTerm lam n



noncomputable def sixVertexAntiferroelectricFreeEnergyValue (lam : ℝ) : ℝ :=
  lam / 2 + sixVertexFreeEnergySeries lam



theorem one_sub_tanh_le_two_mul_exp_neg_two_mul (x : ℝ) :
    1 - Real.tanh x ≤ 2 * Real.exp (-2 * x) := by
  have hformula : 1 - Real.tanh x =
      2 * Real.exp (-x) / (Real.exp x + Real.exp (-x)) := by
    rw [Real.tanh_eq]
    field_simp
    ring
  rw [hformula]
  have hdiv : Real.exp (-x) / (Real.exp x + Real.exp (-x)) ≤
      Real.exp (-x) / Real.exp x := by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _)
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  calc
    2 * Real.exp (-x) / (Real.exp x + Real.exp (-x))
        = 2 * (Real.exp (-x) / (Real.exp x + Real.exp (-x))) := by ring
    _ ≤ 2 * (Real.exp (-x) / Real.exp x) := by gcongr
    _ = 2 * Real.exp (-2 * x) := by
      rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 2
      ring



noncomputable def sixVertexGapCorrectionTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (Real.tanh ((n + 1 : ℝ) * lam) - 1) / (n + 1 : ℝ)


theorem tanh_sub_one_eq_neg_two_mul_exp_neg_two_mul_div (x : ℝ) :
    Real.tanh x - 1 =
      -2 * Real.exp (-2 * x) / (1 + Real.exp (-2 * x)) := by
  rw [Real.tanh_eq]
  have hexp : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hden : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  have hqden : 1 + Real.exp (-2 * x) ≠ 0 := by positivity
  have hcore : Real.exp x * Real.exp (-(x * 2)) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  field_simp [hexp, hden, hqden]
  nlinarith [hcore]



noncomputable def sixVertexGapLambertTerm (lam : ℝ) (n : ℕ) : ℝ :=
  -2 * (-1 : ℝ) ^ (n + 1) *
      Real.exp (-2 * ((n + 1 : ℝ) * lam)) /
    ((n + 1 : ℝ) *
      (1 + Real.exp (-2 * ((n + 1 : ℝ) * lam))))

theorem sixVertexGapCorrectionTerm_eq_lambert (lam : ℝ) (n : ℕ) :
    sixVertexGapCorrectionTerm lam n =
      sixVertexGapLambertTerm lam n := by
  rw [sixVertexGapCorrectionTerm, sixVertexGapLambertTerm,
    tanh_sub_one_eq_neg_two_mul_exp_neg_two_mul_div]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hden :
      1 + Real.exp (-2 * (((n + 1 : ℕ) : ℝ) * lam)) ≠ 0 := by
    positivity
  field_simp [hn, hden]

theorem sixVertexGapCorrectionTerm_norm_le (lam : ℝ) (n : ℕ) :
    ‖sixVertexGapCorrectionTerm lam n‖ ≤
      2 * Real.exp (-2 * lam) ^ (n + 1) := by
  let x : ℝ := (n + 1 : ℝ) * lam
  have htanh : Real.tanh x - 1 ≤ 0 := sub_nonpos.mpr (Real.tanh_lt_one x).le
  have hden : 1 ≤ (n + 1 : ℝ) := by norm_num
  rw [sixVertexGapCorrectionTerm, Real.norm_eq_abs, abs_div, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, abs_of_nonpos htanh,
    abs_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℝ))]
  simp only [one_mul, neg_sub]
  calc
    (1 - Real.tanh x) / (n + 1 : ℝ)
        ≤ (2 * Real.exp (-2 * x)) / (n + 1 : ℝ) := by
          exact div_le_div_of_nonneg_right
            (one_sub_tanh_le_two_mul_exp_neg_two_mul x) (by positivity)
    _ ≤ 2 * Real.exp (-2 * x) := by
      exact div_le_self (by positivity) hden
    _ = 2 * Real.exp (-2 * lam) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 2
      dsimp [x]
      push_cast
      ring

theorem summable_sixVertexGapCorrectionTerm {lam : ℝ} (hlam : 0 < lam) :
    Summable (sixVertexGapCorrectionTerm lam) := by
  have hq0 : 0 ≤ Real.exp (-2 * lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ =>
      2 * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left 2
  exact hgeom.of_norm_bounded (sixVertexGapCorrectionTerm_norm_le lam)



noncomputable def sixVertexGapSeriesTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * Real.tanh ((n + 1 : ℝ) * lam) / (n + 1 : ℝ)

private theorem antitone_one_div_nat_succ :
    Antitone (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) := by
  intro a b hab
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hab 1

noncomputable def sixVertexAlternatingHarmonicLimit : ℝ :=
  Classical.choose (antitone_one_div_nat_succ.tendsto_alternating_series_of_tendsto_zero
    (by simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))

private theorem alternatingHarmonicLimit_tendsto :
    Tendsto (fun N : ℕ => ∑ n ∈ range N,
      (-1 : ℝ) ^ n * ((1 : ℝ) / (n + 1 : ℝ))) atTop
      (𝓝 sixVertexAlternatingHarmonicLimit) :=
  Classical.choose_spec (antitone_one_div_nat_succ.tendsto_alternating_series_of_tendsto_zero
    (by simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))


theorem sixVertexAlternatingHarmonicLimit_eq_log_two :
    sixVertexAlternatingHarmonicLimit = Real.log 2 := by
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    alternatingHarmonicLimit_tendsto
  have hm : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 :=
    tendsto_nhdsWithin_of_tendsto_nhds fun _ h => h
  have habLog :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
        (𝓝[<] 1) (𝓝 sixVertexAlternatingHarmonicLimit) := by
    apply hab.congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hxmin : |-x| < 1 := by
      rw [abs_neg, abs_of_pos hx.1]
      exact hx.2
    have hs := Real.hasSum_pow_div_log_of_abs_lt_one hxmin
    calc
      (∑' n : ℕ, (-1 : ℝ) ^ n * (1 / (n + 1 : ℝ)) * x ^ n) =
          ∑' n : ℕ,
            (-1 / x) * ((-x) ^ (n + 1) / (n + 1 : ℝ)) := by
        apply tsum_congr
        intro n
        rw [pow_succ, neg_pow]
        field_simp [hx0]
        ring
      _ = (-1 / x) *
          ∑' n : ℕ, (-x) ^ (n + 1) / (n + 1 : ℝ) := by
        rw [tsum_mul_left]
      _ = Real.log (1 + x) / x := by
        rw [hs.tsum_eq]
        rw [show 1 - -x = 1 + x by ring]
        field_simp [hx0]
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
        (𝓝[<] 1) (𝓝 (Real.log 2)) := by
    have hc : ContinuousAt (fun x : ℝ => Real.log (1 + x) / x) 1 := by
      exact ((continuousAt_const.add continuousAt_id).log (by norm_num)).div
        continuousAt_id (by norm_num)
    convert hc.tendsto.mono_left hm using 1
    all_goals norm_num
  exact tendsto_nhds_unique habLog hlog


noncomputable def sixVertexGapSeries (lam : ℝ) : ℝ :=
  -Real.log 2 + ∑' n : ℕ, sixVertexGapCorrectionTerm lam n


theorem sixVertexGapSeries_eq_lambert (lam : ℝ) :
    sixVertexGapSeries lam =
      -Real.log 2 +
        ∑' n : ℕ, sixVertexGapLambertTerm lam n := by
  unfold sixVertexGapSeries
  congr 1
  apply tsum_congr
  exact sixVertexGapCorrectionTerm_eq_lambert lam



theorem sixVertexGapSeries_partialSum_tendsto {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, sixVertexGapSeriesTerm lam n) atTop
      (𝓝 (sixVertexGapSeries lam)) := by
  have hharmonic := alternatingHarmonicLimit_tendsto.neg
  rw [sixVertexAlternatingHarmonicLimit_eq_log_two] at hharmonic
  have hcorrection := (summable_sixVertexGapCorrectionTerm hlam).hasSum.tendsto_sum_nat
  have hadd := hharmonic.add hcorrection
  rw [← show -Real.log 2 +
      ∑' n : ℕ, sixVertexGapCorrectionTerm lam n = sixVertexGapSeries lam by rfl]
  apply hadd.congr'
  filter_upwards [] with N
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sixVertexGapSeriesTerm, sixVertexGapCorrectionTerm, pow_succ]
  ring




noncomputable def sixVertexAntiferroelectricGapRate (lam : ℝ) : ℝ :=
  lam + 2 * sixVertexGapSeries lam

end StatMech.FrontierD
