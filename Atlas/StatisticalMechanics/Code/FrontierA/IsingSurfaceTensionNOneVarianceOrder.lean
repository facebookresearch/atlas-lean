/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOneMomentNormalization
import Code.FrontierA.IsingSurfaceTensionNOnePolynomialCertificate









namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

theorem oddPrismTransferBridgeVarianceSkewNumerator_one_nonpos
    (beta r : Real) (hbeta : 0 ≤ beta) (hr : 0 ≤ r) :
    oddPrismTransferBridgeVarianceSkewNumerator beta 1 r ≤ 0 := by
  rw [oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_rawMomentPoly]
  apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
  apply reflectedVarianceSkewPoly_eval_nonpos
  · exact Real.one_le_exp (mul_nonneg (by norm_num) hbeta)
  · exact Real.one_le_exp (mul_nonneg (by norm_num) hr)

theorem oddPrismTransferBridgeVariance_one_le_neg
    (beta r : Real) (hbeta : 0 ≤ beta) (hr : 0 ≤ r) :
    oddPrismTransferBridgeVariance beta 1 r ≤
      oddPrismTransferBridgeVariance beta 1 (-r) := by
  rw [oddPrismTransferBridgeVariance_le_neg_iff_skewNumerator_nonpos
    beta 1 (by omega) r]
  exact oddPrismTransferBridgeVarianceSkewNumerator_one_nonpos
    beta r hbeta hr

theorem oddPrismUnequalBridgeSymmetricMeanOrder_one
    (beta : Real) (hbeta : 0 ≤ beta) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta 1 := by
  apply oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_Icc hbeta
  intro r hr hrbeta
  rw [oddPrismUnequalBridgeVariance_eq_transfer beta 1 (by omega) r,
    oddPrismUnequalBridgeVariance_eq_transfer beta 1 (by omega) (-r)]
  exact oddPrismTransferBridgeVariance_one_le_neg beta r hbeta hr

end StatMech.FrontierA.NOneSymmetricMeanCertificate
