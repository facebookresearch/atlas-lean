/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.FrontierD.SixVertexAntiferroelectricSeries

namespace StatMech.FrontierD


noncomputable def fkQgt4SixVertexWeight (q : ℝ) : ℝ :=
  Real.sqrt (2 + Real.sqrt q)

theorem fkQgt4SixVertexWeight_sq {q : ℝ} (hq : 4 < q) :
    fkQgt4SixVertexWeight q ^ 2 = 2 + Real.sqrt q := by
  rw [fkQgt4SixVertexWeight, Real.sq_sqrt]
  have hq0 : 0 ≤ q := by linarith
  have hsqrt : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  linarith


theorem two_lt_fkQgt4SixVertexWeight {q : ℝ} (hq : 4 < q) :
    2 < fkQgt4SixVertexWeight q := by
  have hq0 : 0 ≤ q := by linarith
  have hsqrtq : 2 < Real.sqrt q := by
    nlinarith [Real.sq_sqrt hq0, Real.sqrt_nonneg q]
  have harg : 0 ≤ 2 + Real.sqrt q := by positivity
  rw [fkQgt4SixVertexWeight]
  nlinarith [Real.sq_sqrt harg, Real.sqrt_nonneg (2 + Real.sqrt q)]



theorem cosh_sixVertexAntiferroelectricLambda_fkQgt4 {q : ℝ} (hq : 4 < q) :
    Real.cosh
        (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) =
      Real.sqrt q / 2 := by
  rw [sixVertex_cosh_antiferroelectricLambda
    (two_lt_fkQgt4SixVertexWeight hq), fkQgt4SixVertexWeight_sq hq]
  ring


theorem sixVertexAntiferroelectricLambda_fkQgt4_pos {q : ℝ} (hq : 4 < q) :
    0 < sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) :=
  sixVertexAntiferroelectricLambda_pos (two_lt_fkQgt4SixVertexWeight hq)

end StatMech.FrontierD
