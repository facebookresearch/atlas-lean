/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRapidityTrigonometry
import Code.FrontierD.SixVertexBetheRootDensityUniqueness





namespace StatMech.FrontierD

noncomputable section

theorem sixVertexAnisotropyMagnitude_eq_cosh_lambda
    {c : Real} (hc : 2 < c) :
    sixVertexAnisotropyMagnitude c =
      Real.cosh (sixVertexAntiferroelectricLambda c) := by
  rw [sixVertex_cosh_antiferroelectricLambda hc]
  unfold sixVertexAnisotropyMagnitude sixVertexDelta
  ring

theorem sixVertexRootDensityScale_eq_sinh_lambda
    {c : Real} (hc : 2 < c) :
    sixVertexRootDensityScale c =
      Real.sinh (sixVertexAntiferroelectricLambda c) := by
  let lam := sixVertexAntiferroelectricLambda c
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hd : sixVertexAnisotropyMagnitude c = Real.cosh lam :=
    sixVertexAnisotropyMagnitude_eq_cosh_lambda hc
  unfold sixVertexRootDensityScale
  rw [hd, <- Real.sinh_sq]
  exact Real.sqrt_sq (Real.sinh_pos_iff.mpr hlam).le



theorem sixVertexRootDensityWeight_rapidityMomentum
    {c : Real} (hc : 2 < c) (alpha : Real) :
    sixVertexRootDensityWeight c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      sixVertexXiFourier (sixVertexAntiferroelectricLambda c) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let d := Real.cosh lam
  let s := Real.sinh lam
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hd : sixVertexAnisotropyMagnitude c = d :=
    sixVertexAnisotropyMagnitude_eq_cosh_lambda hc
  have hs : sixVertexRootDensityScale c = s :=
    sixVertexRootDensityScale_eq_sinh_lambda hc
  have hdelta : sixVertexDelta c = -d := by
    unfold sixVertexAnisotropyMagnitude at hd
    linarith
  have hspos : 0 < s := Real.sinh_pos_iff.mpr hlam
  have hden : 0 < d - Real.cos alpha := by
    have hd1 : 1 < d := by
      dsimp [d]
      exact Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  rw [sixVertexXiFourier_eq hlam]
  unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
  rw [hdelta, hs, cos_sixVertexRapidityMomentum hlam]
  dsimp [d, s]
  have hden' : Real.cosh lam - Real.cos alpha ≠ 0 := by
    dsimp [d] at hden
    exact hden.ne'
  have hs' : Real.sinh lam ≠ 0 := by
    dsimp [s] at hspos
    exact hspos.ne'
  field_simp [hs', hden']
  nlinarith [Real.sinh_sq lam]



theorem sixVertexRootDensityKernel_rapidityMomentum
    {c : Real} (hc : 2 < c) (alpha beta : Real) :
    sixVertexRootDensityKernel c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha)
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) beta) =
      sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
        (alpha - beta) := by
  let lam := sixVertexAntiferroelectricLambda c
  let d := Real.cosh lam
  let s := Real.sinh lam
  let Da := d - Real.cos alpha
  let Db := d - Real.cos beta
  let x := sixVertexRapidityMomentum lam alpha
  let y := sixVertexRapidityMomentum lam beta
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have h2lam : 0 < 2 * lam := mul_pos (by norm_num) hlam
  have hd : sixVertexAnisotropyMagnitude c = d :=
    sixVertexAnisotropyMagnitude_eq_cosh_lambda hc
  have hs : sixVertexRootDensityScale c = s :=
    sixVertexRootDensityScale_eq_sinh_lambda hc
  have hdelta : sixVertexDelta c = -d := by
    unfold sixVertexAnisotropyMagnitude at hd
    linarith
  have hd1 : 1 < d := by
    dsimp [d]
    exact Real.one_lt_cosh.mpr hlam.ne'
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sinh_pos_iff.mpr hlam
  have hDa : 0 < Da := by
    dsimp [Da]
    linarith [Real.cos_le_one alpha]
  have hDb : 0 < Db := by
    dsimp [Db]
    linarith [Real.cos_le_one beta]
  have hsq : s ^ 2 = d ^ 2 - 1 := by
    dsimp [s, d]
    exact Real.sinh_sq lam
  have hFx : sixVertexBetheIntegratingFactor c x = s ^ 2 / Da := by
    unfold sixVertexBetheIntegratingFactor
    rw [hdelta]
    dsimp [x]
    rw [cos_sixVertexRapidityMomentum hlam]
    change (d * Real.cos alpha - 1) / Da - -d = s ^ 2 / Da
    field_simp [hDa.ne']
    nlinarith [hsq]
  have hFy : sixVertexBetheIntegratingFactor c y = s ^ 2 / Db := by
    unfold sixVertexBetheIntegratingFactor
    rw [hdelta]
    dsimp [y]
    rw [cos_sixVertexRapidityMomentum hlam]
    change (d * Real.cos beta - 1) / Db - -d = s ^ 2 / Db
    field_simp [hDb.ne']
    nlinarith [hsq]
  have hcosxy : Real.cos (x - y) =
      ((d * Real.cos alpha - 1) * (d * Real.cos beta - 1) +
        s ^ 2 * Real.sin alpha * Real.sin beta) / (Da * Db) := by
    rw [Real.cos_sub]
    dsimp [x, y]
    rw [cos_sixVertexRapidityMomentum hlam,
      cos_sixVertexRapidityMomentum hlam,
      sin_sixVertexRapidityMomentum hlam,
      sin_sixVertexRapidityMomentum hlam]
    dsimp [Da, Db, d, s]
    field_simp [hDa.ne', hDb.ne']
  have htheta : sixVertexThetaDerivativeDenominator c x y =
      4 * (s ^ 2 / Da) * (s ^ 2 / Db) +
        2 * (1 - ((d * Real.cos alpha - 1) *
          (d * Real.cos beta - 1) +
            s ^ 2 * Real.sin alpha * Real.sin beta) / (Da * Db)) := by
    rw [sixVertexThetaDerivativeDenominator_eq, hFx, hFy, hcosxy]
  have hthetaPos : 0 < sixVertexThetaDerivativeDenominator c x y :=
    sixVertexThetaDerivativeDenominator_pos hc x y
  let Q := d ^ 2 + s ^ 2 -
    Real.cos alpha * Real.cos beta - Real.sin alpha * Real.sin beta
  have hthetaSimple : sixVertexThetaDerivativeDenominator c x y =
      2 * s ^ 2 * Q / (Da * Db) := by
    rw [htheta]
    dsimp [Q]
    rw [hsq]
    field_simp [hDa.ne', hDb.ne']
    ring
  have hRhsDen : 0 < Real.cosh (2 * lam) - Real.cos (alpha - beta) := by
    have hcosh : 1 < Real.cosh (2 * lam) :=
      Real.one_lt_cosh.mpr h2lam.ne'
    linarith [Real.cos_le_one (alpha - beta)]
  have hQpos : 0 < Q := by
    dsimp [Q, d, s]
    rw [Real.cosh_two_mul, Real.cos_sub] at hRhsDen
    nlinarith
  rw [sixVertexXiFourier_eq h2lam]
  change sixVertexRootDensityKernel c x y = _
  unfold sixVertexRootDensityKernel
  rw [hd, hs, hFx, hFy, hthetaSimple, Real.sinh_two_mul,
    Real.cosh_two_mul, Real.cos_sub]
  change 4 * d * (s ^ 2 / Da) * (s ^ 2 / Db) /
      (s * (2 * s ^ 2 * Q / (Da * Db))) =
    2 * s * d /
      (d ^ 2 + s ^ 2 -
        (Real.cos alpha * Real.cos beta + Real.sin alpha * Real.sin beta))
  rw [show d ^ 2 + s ^ 2 -
      (Real.cos alpha * Real.cos beta + Real.sin alpha * Real.sin beta) = Q by
    dsimp [Q]
    ring]
  field_simp [hspos.ne', hDa.ne', hDb.ne', hQpos.ne']
  ring

end

end StatMech.FrontierD
