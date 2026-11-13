/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics
import Code.FrontierA.IsingSurfaceTensionNOneFactorCheckCleared
import Code.FrontierA.IsingSurfaceTensionNOneFactorCheckProduct
import Code.FrontierA.IsingSurfaceTensionNOneFactorCheckShift








namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

theorem generatedQuotientPoly_eval_nonneg
    (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    0 ≤ generatedQuotientPoly.eval X Y := by
  have hshift : 0 ≤ generatedShiftedQuotientPoly.eval (X - 1) (Y - 1) :=
    BiPoly.eval_nonneg_of_coeff_nonneg generatedShiftedQuotientPoly
      (X - 1) (Y - 1) (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)
      generatedShiftedQuotientPoly_coefficients_nonnegative
  rw [← generatedQuotientPoly_shiftToOne,
    BiPoly.eval_shiftToOne generatedQuotientPoly (X - 1) (Y - 1)
      generatedQuotientPoly_exponents_nonnegative] at hshift
  simpa only [add_sub_cancel_left] using hshift

theorem clearedSkewPoly_eval_eq_generated_factors
    (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0) :
    clearedSkewPoly.eval X Y =
      generatedQuotientPoly.eval X Y * (X ^ 2 - 1) * (Y ^ 2 - 1) := by
  rw [clearedSkewPoly_eq_generated, generatedClearedSkewPoly_eq_factors,
    BiPoly.eval_mul X Y hX hY, BiPoly.eval_mul X Y hX hY]
  have hx : BiPoly.xSquareSubOne.eval X Y = X ^ 2 - 1 := by
    rw [BiPoly.xSquareSubOne, BiPoly.eval_ofTerms]
    simp [BiTerm.eval]
  have hy : BiPoly.ySquareSubOne.eval X Y = Y ^ 2 - 1 := by
    rw [BiPoly.ySquareSubOne, BiPoly.eval_ofTerms]
    simp [BiTerm.eval]
  rw [hx, hy]

theorem reflectedVarianceSkewPoly_eval_nonpos
    (X Y : Real) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    reflectedVarianceSkewPoly.eval X Y ≤ 0 := by
  have hX0 : X ≠ 0 := ne_of_gt (_root_.lt_of_lt_of_le zero_lt_one hX)
  have hY0 : Y ≠ 0 := ne_of_gt (_root_.lt_of_lt_of_le zero_lt_one hY)
  exact eval_reflectedVarianceSkewPolyOf_nonpos_of_explicit_factor
    rawMomentPoly generatedQuotientPoly X Y hX hY
      (clearedSkewPoly_eval_eq_generated_factors X Y hX0 hY0)
      (generatedQuotientPoly_eval_nonneg X Y hX hY)

end StatMech.FrontierA.NOneSymmetricMeanCertificate
