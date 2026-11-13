/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierD.FKQgt4NearFourParameterAsymptotic

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexAntiferroelectricFreeEnergy_partialSum_tendsto
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (fun N : Nat =>
      lam / 2 + ∑ n ∈ range N, sixVertexFreeEnergySeriesTerm lam n)
      atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
  have hsum :=
    (summable_sixVertexFreeEnergySeriesTerm hlam).hasSum.tendsto_sum_nat
  simpa [sixVertexAntiferroelectricFreeEnergyValue,
    sixVertexFreeEnergySeries] using (tendsto_const_nhds.add hsum)



theorem sixVertexAntiferroelectricGapRate_eq_dualPowerSeries
    {lam : Real} (hlam : 0 < lam) :
    sixVertexAntiferroelectricGapRate lam =
      sixVertexDualGapPowerSeries
        (Real.exp (-(Real.pi ^ 2) / (2 * lam))) := by
  rw [sixVertexAntiferroelectricGapRate_eq_dualGapRate hlam,
    sixVertexDualGapRate]



theorem sixVertexAntiferroelectricGapRate_pos
    {lam : Real} (hlam : 0 < lam) :
    0 < sixVertexAntiferroelectricGapRate lam := by
  let x := Real.exp (-(Real.pi ^ 2) / (2 * lam))
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hden : 0 < 2 * lam := by positivity
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hpi) hden
  rw [sixVertexAntiferroelectricGapRate_eq_dualPowerSeries hlam]
  exact (mul_pos (by norm_num) hx0).trans_le
    (sixVertexDualGapPowerSeries_lower hx0.le hx1)



theorem sixVertexAntiferroelectricGapFactor_mem_Ioo
    {lam : Real} (hlam : 0 < lam) {r : Nat} (hr : 1 <= r) :
    Real.exp (-(r : Real) * sixVertexAntiferroelectricGapRate lam) ∈
      Set.Ioo 0 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_lt_one_iff]
  have hr0 : 0 < (r : Real) := by exact_mod_cast (show 0 < r by omega)
  have hgap := sixVertexAntiferroelectricGapRate_pos hlam
  nlinarith



theorem sixVertexCanonicalGapRate_pos {c : Real} (hc : 2 < c) :
    0 < sixVertexAntiferroelectricGapRate
      (sixVertexAntiferroelectricLambda c) :=
  sixVertexAntiferroelectricGapRate_pos
    (sixVertexAntiferroelectricLambda_pos hc)



theorem fkQgt4SixVertexGapRate_pos {q : Real} (hq : 4 < q) :
    0 < fkQgt4SixVertexGapRate q := by
  unfold fkQgt4SixVertexGapRate
  exact sixVertexAntiferroelectricGapRate_pos
    (sixVertexAntiferroelectricLambda_fkQgt4_pos hq)

end

end StatMech.FrontierD
