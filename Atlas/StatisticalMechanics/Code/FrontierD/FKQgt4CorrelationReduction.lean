/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















import Code.FrontierD.FKQgt4ParameterBridge

namespace StatMech.FrontierD


noncomputable def fkQgt4SixVertexGapRate (q : ℝ) : ℝ :=
  sixVertexAntiferroelectricGapRate
    (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))








def FKQgt4WindingSectorBounds (xiInv R : ℝ) : Prop :=
  R ≤ xiInv ∧
    ∀ r : ℕ, 2 ≤ r → ((r - 1 : ℕ) : ℝ) * xiInv ≤ (r : ℝ) * R




theorem eq_of_windingSectorBounds {xiInv R : ℝ}
    (h : FKQgt4WindingSectorBounds xiInv R) :
    xiInv = R := by
  obtain ⟨hlower, hupper⟩ := h
  apply le_antisymm ?_ hlower
  by_contra! hlt
  have hgap : 0 < xiInv - R := sub_pos.mpr hlt
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (R / (xiInv - R) + 1)
  let r := n + 2
  have hr : 2 ≤ r := by omega
  have hu := hupper r hr
  have hn' : R < (n + 1 : ℝ) * (xiInv - R) := by
    have hbase : R / (xiInv - R) < (n : ℝ) := by linarith
    rw [div_lt_iff₀ hgap] at hbase
    nlinarith
  dsimp [r] at hu
  push_cast at hu
  nlinarith



theorem fkQgt4_inverseCorrelation_eq_sixVertexGapRate {q xiInv : ℝ}
    (h : FKQgt4WindingSectorBounds xiInv (fkQgt4SixVertexGapRate q)) :
    xiInv = fkQgt4SixVertexGapRate q :=
  eq_of_windingSectorBounds h



theorem fkQgt4SixVertexGapRate_pos_of_inverseCorrelation {q xiInv : ℝ}
    (hxi : 0 < xiInv)
    (h : FKQgt4WindingSectorBounds xiInv (fkQgt4SixVertexGapRate q)) :
    0 < fkQgt4SixVertexGapRate q := by
  rwa [← fkQgt4_inverseCorrelation_eq_sixVertexGapRate h]



theorem fkQgt4_sub_four_eq_four_mul_sinh_sq {q : ℝ} (hq : 4 < q) :
    q - 4 = 4 *
      Real.sinh
        (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) ^ 2 := by
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  have hc := cosh_sixVertexAntiferroelectricLambda_fkQgt4 hq
  have hq0 : 0 ≤ q := by linarith
  have hsqrt := Real.sq_sqrt hq0
  have hid := Real.cosh_sq_sub_sinh_sq lam
  change q - 4 = 4 * Real.sinh lam ^ 2
  change Real.cosh lam = Real.sqrt q / 2 at hc
  have hc2 : 4 * Real.cosh lam ^ 2 = q := by
    rw [hc]
    nlinarith
  nlinarith



theorem sqrt_fkQgt4_sub_four_eq_two_mul_sinh {q : ℝ} (hq : 4 < q) :
    Real.sqrt (q - 4) =
      2 * Real.sinh
        (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) := by
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  have hq4 : 0 ≤ q - 4 := by linarith
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_fkQgt4_pos hq
  have hsinh : 0 ≤ Real.sinh lam := (Real.sinh_pos_iff.mpr hlam).le
  apply (Real.sqrt_eq_iff_eq_sq hq4 (mul_nonneg (by norm_num) hsinh)).2
  rw [show q - 4 = 4 * Real.sinh lam ^ 2 by
    exact fkQgt4_sub_four_eq_four_mul_sinh_sq hq]
  ring



theorem fkQgt4_exponentialScale_eq {q : ℝ} (hq : 4 < q) :
    Real.pi ^ 2 / Real.sqrt (q - 4) =
      Real.pi ^ 2 /
        (2 * Real.sinh
          (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))) := by
  rw [sqrt_fkQgt4_sub_four_eq_two_mul_sinh hq]

end StatMech.FrontierD
