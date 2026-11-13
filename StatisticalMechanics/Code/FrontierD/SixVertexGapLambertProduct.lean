/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierD.SixVertexAntiferroelectricSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open Finset Filter Topology

namespace StatMech.FrontierD



noncomputable def sixVertexGapAlternatingLogSeries (lam : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n *
    Real.log (1 + Real.exp (-2 * ((n + 1 : ℝ) * lam)))

private noncomputable def gapLogDoubleTerm (q : ℝ) (p : ℕ × ℕ) : ℝ :=
  (-1 : ℝ) ^ p.1 * (-1 : ℝ) ^ p.2 *
    q ^ ((p.1 + 1) * (p.2 + 1)) / (p.2 + 1 : ℝ)

private theorem summable_gapLogDoubleTerm {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (gapLogDoubleTerm q) := by
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq0 hq1
  have hprod : Summable (fun p : ℕ × ℕ => q ^ p.1 * q ^ p.2) :=
    hgeom.mul_of_nonneg hgeom (fun _ => pow_nonneg hq0 _) (fun _ => pow_nonneg hq0 _)
  have hmajor : Summable (fun p : ℕ × ℕ => q * (q ^ p.1 * q ^ p.2)) :=
    hprod.mul_left q
  apply hmajor.of_norm_bounded
  intro p
  rw [gapLogDoubleTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_pow, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (pow_nonneg hq0 _), abs_of_nonneg (by positivity : (0 : ℝ) ≤ p.2 + 1)]
  simp only [one_pow, one_mul]
  have hden : 1 ≤ (p.2 + 1 : ℝ) := by norm_num
  calc
    q ^ ((p.1 + 1) * (p.2 + 1)) / (p.2 + 1 : ℝ)
        ≤ q ^ ((p.1 + 1) * (p.2 + 1)) := div_le_self (pow_nonneg hq0 _) hden
    _ ≤ q ^ (p.1 + p.2 + 1) := by
      apply pow_le_pow_of_le_one hq0 hq1.le
      nlinarith [Nat.zero_le (p.1 * p.2)]
    _ = q * (q ^ p.1 * q ^ p.2) := by
      rw [pow_add, pow_add]
      ring

private theorem gapLogTaylor_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    HasSum
      (fun n : ℕ => (-1 : ℝ) ^ m * (-1 : ℝ) ^ n *
        q ^ ((m + 1) * (n + 1)) / (n + 1 : ℝ))
      ((-1 : ℝ) ^ m * Real.log (1 + q ^ (m + 1))) := by
  have hx0 : 0 ≤ q ^ (m + 1) := pow_nonneg hq0 _
  have hx1 : q ^ (m + 1) < 1 := by
    exact pow_lt_one₀ hq0 hq1 (by positivity)
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (x := -(q ^ (m + 1))) (by simpa [abs_of_nonneg hx0] using hx1)).neg
  have hm := h.mul_left ((-1 : ℝ) ^ m)
  convert hm using 1
  · ext n
    rw [neg_pow, pow_mul]
    ring
  · rw [sub_neg_eq_add]
    ring

private theorem gapLogGeometric_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    HasSum
      (fun m : ℕ => (-1 : ℝ) ^ m * (-1 : ℝ) ^ n *
        q ^ ((m + 1) * (n + 1)) / (n + 1 : ℝ))
      ((-1 : ℝ) ^ n * q ^ (n + 1) /
        ((n + 1 : ℝ) * (1 + q ^ (n + 1)))) := by
  have hqpow0 : 0 ≤ q ^ (n + 1) := pow_nonneg hq0 _
  have hqpow1 : q ^ (n + 1) < 1 := pow_lt_one₀ hq0 hq1 (by positivity)
  have hgeom := hasSum_geometric_of_norm_lt_one (ξ := -(q ^ (n + 1))) (by
    simpa only [Real.norm_eq_abs, abs_neg, abs_pow, abs_of_nonneg hq0] using hqpow1)
  have hmul := hgeom.mul_left
    (((-1 : ℝ) ^ n * q ^ (n + 1)) / (n + 1 : ℝ))
  convert hmul using 1
  · ext m
    rw [Nat.add_mul, pow_add, pow_mul, neg_pow]
    simp only [one_mul]
    ring
  · have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hden : 1 + q ^ (n + 1) ≠ 0 := by positivity
    rw [sub_neg_eq_add]
    field_simp [hn, hden]



theorem tsum_sixVertexGapLambertTerm_eq_two_mul_alternatingLog
    {lam : ℝ} (hlam : 0 < lam) :
    (∑' n : ℕ, sixVertexGapLambertTerm lam n) =
      2 * sixVertexGapAlternatingLogSeries lam := by
  let q := Real.exp (-2 * lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hdouble := summable_gapLogDoubleTerm hq0 hq1
  have hrows :
      (∑' m : ℕ, ∑' n : ℕ, gapLogDoubleTerm q (m, n)) =
        sixVertexGapAlternatingLogSeries lam := by
    rw [sixVertexGapAlternatingLogSeries]
    apply tsum_congr
    intro m
    change (∑' n : ℕ, (-1 : ℝ) ^ m * (-1 : ℝ) ^ n *
      q ^ ((m + 1) * (n + 1)) / (n + 1 : ℝ)) = _
    rw [(gapLogTaylor_hasSum hq0 hq1 m).tsum_eq]
    congr 2
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hcols :
      (∑' n : ℕ, ∑' m : ℕ, gapLogDoubleTerm q (m, n)) =
        (1 / 2 : ℝ) * ∑' n : ℕ, sixVertexGapLambertTerm lam n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    change (∑' m : ℕ, (-1 : ℝ) ^ m * (-1 : ℝ) ^ n *
      q ^ ((m + 1) * (n + 1)) / (n + 1 : ℝ)) = _
    rw [(gapLogGeometric_hasSum hq0 hq1 n).tsum_eq]
    rw [sixVertexGapLambertTerm]
    dsimp [q]
    have hexp : Real.exp (-2 * ((n + 1 : ℝ) * lam)) =
        Real.exp (-2 * lam) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp]
    field_simp
    ring
  have hcomm :
      (∑' m : ℕ, ∑' n : ℕ, gapLogDoubleTerm q (m, n)) =
        ∑' n : ℕ, ∑' m : ℕ, gapLogDoubleTerm q (m, n) := by
    have hdouble' : Summable (Function.uncurry
        (fun m n : ℕ => gapLogDoubleTerm q (m, n))) := by
      simpa [Function.uncurry] using hdouble
    exact hdouble'.tsum_comm.symm
  rw [hrows, hcols] at hcomm
  linarith



theorem sixVertexAntiferroelectricGapRate_eq_logProduct
    {lam : ℝ} (hlam : 0 < lam) :
    sixVertexAntiferroelectricGapRate lam =
      lam - 2 * Real.log 2 + 4 * sixVertexGapAlternatingLogSeries lam := by
  rw [sixVertexAntiferroelectricGapRate, sixVertexGapSeries_eq_lambert,
    tsum_sixVertexGapLambertTerm_eq_two_mul_alternatingLog hlam]
  ring

end StatMech.FrontierD
