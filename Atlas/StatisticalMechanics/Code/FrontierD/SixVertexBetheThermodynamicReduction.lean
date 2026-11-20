/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.FrontierD.SixVertexAntiferroelectricSeries

open Finset Matrix Filter Topology

namespace StatMech.FrontierD



def sixVertexFourWidth (r k : ℕ) : ℕ := 4 * (r + k + 1)

theorem sixVertexFourWidth_pos (r k : ℕ) : 0 < sixVertexFourWidth r k := by
  unfold sixVertexFourWidth
  omega

theorem sixVertexFourWidth_even (r k : ℕ) : Even (sixVertexFourWidth r k) := by
  unfold sixVertexFourWidth Even
  use 2 * (r + k + 1)
  omega

theorem sixVertexFourWidth_charge_le (r k : ℕ) :
    r ≤ sixVertexFourWidth r k / 2 := by
  unfold sixVertexFourWidth
  omega


noncomputable def sixVertexLambdaAlongFour (c : ℝ) (r k : ℕ) : ℝ :=
  sixVertexLambda (sixVertexFourWidth r k) r
    (sixVertexFourWidth_even r k) (sixVertexFourWidth_charge_le r k) c

theorem sixVertexLambdaAlongFour_pos {c : ℝ} (hc : 0 < c) (r k : ℕ) :
    0 < sixVertexLambdaAlongFour c r k := by
  exact (sixVertexLambda_isPerronFrobenius
    (sixVertexFourWidth r k) r (sixVertexFourWidth_even r k)
    (sixVertexFourWidth_charge_le r k) hc).1


noncomputable def sixVertexCentralWidthRate (c : ℝ) (k : ℕ) : ℝ :=
  Real.log (sixVertexLambdaAlongFour c 0 k) / (sixVertexFourWidth 0 k : ℝ)


noncomputable def sixVertexFixedChargeRatio (c : ℝ) (r k : ℕ) : ℝ :=
  sixVertexLambdaAlongFour c r k /
    sixVertexLambda (sixVertexFourWidth r k) 0
      (sixVertexFourWidth_even r k) (Nat.zero_le _) c


noncomputable def sixVertexFixedChargeLogRatio (c : ℝ) (r k : ℕ) : ℝ :=
  Real.log (sixVertexFixedChargeRatio c r k)

theorem sixVertexFixedChargeRatio_pos {c : ℝ} (hc : 0 < c) (r k : ℕ) :
    0 < sixVertexFixedChargeRatio c r k := by
  apply div_pos (sixVertexLambdaAlongFour_pos hc r k)
  exact (sixVertexLambda_isPerronFrobenius
    (sixVertexFourWidth r k) 0 (sixVertexFourWidth_even r k)
    (Nat.zero_le _) hc).1



theorem sixVertexFixedChargeLogRatio_eq {c : ℝ} (hc : 0 < c) (r k : ℕ) :
    sixVertexFixedChargeLogRatio c r k =
      Real.log (sixVertexLambdaAlongFour c r k) -
        Real.log (sixVertexLambda (sixVertexFourWidth r k) 0
          (sixVertexFourWidth_even r k) (Nat.zero_le _) c) := by
  rw [sixVertexFixedChargeLogRatio, sixVertexFixedChargeRatio, Real.log_div]
  · exact (sixVertexLambdaAlongFour_pos hc r k).ne'
  · exact ((sixVertexLambda_isPerronFrobenius
      (sixVertexFourWidth r k) 0 (sixVertexFourWidth_even r k)
      (Nat.zero_le _) hc).1).ne'



theorem sixVertexFixedChargeTraceLogRatio_div_height_tendsto
    {c : Real} (hc : 0 < c) (r k : Nat) :
    Tendsto (fun M : Nat =>
      Real.log
          (Matrix.trace
                (sixVertexSectorTransfer (sixVertexFourWidth r k)
                  (sixVertexFourWidth r k / 2 - r) c ^ M) /
            Matrix.trace
                (sixVertexSectorTransfer (sixVertexFourWidth r k)
                  (sixVertexFourWidth r k / 2) c ^ M)) /
        (M : Real))
      atTop
      (nhds (sixVertexFixedChargeLogRatio c r k)) := by
  have h := sixVertexLambda_log_trace_ratio_div_height_tendsto
    (sixVertexFourWidth r k) r (sixVertexFourWidth_even r k)
      (sixVertexFourWidth_charge_le r k) hc
  simpa only [sixVertexFixedChargeLogRatio, sixVertexFixedChargeRatio,
    sixVertexLambdaAlongFour] using h



theorem sixVertexFixedChargeRatio_tendsto_iff_logRatio
    {c L : ℝ} (hc : 0 < c) (r : ℕ) :
    Tendsto (sixVertexFixedChargeRatio c r) atTop (nhds (Real.exp L)) ↔
      Tendsto (sixVertexFixedChargeLogRatio c r) atTop (nhds L) := by
  constructor
  · intro h
    have hlog := (Real.continuousAt_log (Real.exp_ne_zero L)).tendsto.comp h
    simpa [sixVertexFixedChargeLogRatio] using hlog
  · intro h
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp h
    apply hexp.congr'
    filter_upwards [] with k
    exact Real.exp_log (sixVertexFixedChargeRatio_pos hc r k)



theorem sixVertexAntiferroelectricGapFormula_iff_logBethe
    {c lam : ℝ} (hc : 0 < c) (r : ℕ) :
    Tendsto (sixVertexFixedChargeRatio c r) atTop
        (nhds (Real.exp (-(r : ℝ) *
          sixVertexAntiferroelectricGapRate lam))) ↔
      Tendsto (sixVertexFixedChargeLogRatio c r) atTop
        (nhds (-(r : ℝ) * sixVertexAntiferroelectricGapRate lam)) := by
  exact sixVertexFixedChargeRatio_tendsto_iff_logRatio hc r


noncomputable def sixVertexBalancedSectorPartitionSum
    (N M : ℕ) (c : ℝ) : ℝ :=
  Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M)



noncomputable def sixVertexBalancedAreaDensity (c : ℝ) (k M : ℕ) : ℝ :=
  Real.log (sixVertexBalancedSectorPartitionSum (sixVertexFourWidth 0 k) M c) /
    ((sixVertexFourWidth 0 k : ℝ) * (M : ℝ))



theorem sixVertexBalancedAreaDensity_tendsto_widthRate
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (sixVertexBalancedAreaDensity c k) atTop
      (nhds (sixVertexCentralWidthRate c k)) := by
  let N := sixVertexFourWidth 0 k
  have h := sixVertexLambda_log_trace_div_height_tendsto
    N 0 (sixVertexFourWidth_even 0 k) (Nat.zero_le _) hc
  have hdiv := h.div_const (N : ℝ)
  have hdiv' : Tendsto (fun M : ℕ =>
      Real.log (Matrix.trace (sixVertexSectorTransfer N (N / 2 - 0) c ^ M)) /
        (M : ℝ) / (N : ℝ)) atTop
      (nhds (sixVertexCentralWidthRate c k)) := by
    simpa [sixVertexCentralWidthRate, sixVertexLambdaAlongFour, N] using hdiv
  apply hdiv'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  unfold sixVertexBalancedAreaDensity sixVertexBalancedSectorPartitionSum
  dsimp [N]
  field_simp



def SixVertexHasIteratedLimit (F : ℕ → ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ g : ℕ → ℝ, (∀ k, Tendsto (F k) atTop (nhds (g k))) ∧
    Tendsto g atTop (nhds a)



theorem sixVertexBalanced_iteratedLimit_iff_widthRate
    {c a : ℝ} (hc : 0 < c) :
    SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c) a ↔
      Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) := by
  constructor
  · rintro ⟨g, hg, hga⟩
    have heq : g = sixVertexCentralWidthRate c := by
      funext k
      exact tendsto_nhds_unique (hg k)
        (sixVertexBalancedAreaDensity_tendsto_widthRate hc k)
    simpa [heq] using hga
  · intro h
    exact ⟨sixVertexCentralWidthRate c,
      sixVertexBalancedAreaDensity_tendsto_widthRate hc, h⟩



theorem sixVertexAntiferroelectricFreeEnergyFormula_iff_widthBethe
    {c lam : ℝ} (hc : 0 < c) :
    SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c)
        (sixVertexAntiferroelectricFreeEnergyValue lam) ↔
      Tendsto (sixVertexCentralWidthRate c) atTop
        (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
  exact sixVertexBalanced_iteratedLimit_iff_widthRate hc

end StatMech.FrontierD
