/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierD.SixVertexBetheVariational









namespace StatMech.FrontierD

noncomputable section

theorem sixVertexThetaDerivativeDenominator_reflect_left_sub
    (c x y : Real) :
    sixVertexThetaDerivativeDenominator c (-x) y -
        sixVertexThetaDerivativeDenominator c x y =
      4 * Real.sin x * Real.sin y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  rw [Real.cos_neg, Real.sin_neg]
  ring



theorem sixVertexTheta_right_difference_nonneg
    {c x y : Real} (hc : 2 < c)
    (hx : x ∈ Set.Icc (-Real.pi) 0)
    (hy : y ∈ Set.Icc (-Real.pi) 0) :
    0 <=
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
          sixVertexThetaDerivativeDenominator c x y) -
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-x) /
          sixVertexThetaDerivativeDenominator c (-x) y) := by
  have hdelta : sixVertexDelta c < 0 :=
    (sixVertexDelta_lt_neg_one hc).trans (by norm_num)
  have hfactor : 0 < sixVertexBetheIntegratingFactor c x :=
    sixVertexBetheIntegratingFactor_pos hc x
  have hscale : 0 <= -4 * sixVertexDelta c := by nlinarith
  have hnum : 0 <= -4 * sixVertexDelta c *
      sixVertexBetheIntegratingFactor c x :=
    mul_nonneg hscale hfactor.le
  have hsinx : Real.sin x <= 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hx.2 hx.1
  have hsiny : Real.sin y <= 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hy.2 hy.1
  have hdenle : sixVertexThetaDerivativeDenominator c x y <=
      sixVertexThetaDerivativeDenominator c (-x) y := by
    rw [← sub_nonneg]
    rw [sixVertexThetaDerivativeDenominator_reflect_left_sub]
    have hp : 0 <= Real.sin x * Real.sin y :=
      mul_nonneg_of_nonpos_of_nonpos hsinx hsiny
    nlinarith
  have hdenpos : 0 < sixVertexThetaDerivativeDenominator c x y :=
    sixVertexThetaDerivativeDenominator_pos hc x y
  have hreflectpos : 0 < sixVertexThetaDerivativeDenominator c (-x) y :=
    sixVertexThetaDerivativeDenominator_pos hc (-x) y
  have hquot :
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x) /
          sixVertexThetaDerivativeDenominator c (-x) y <=
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x) /
          sixVertexThetaDerivativeDenominator c x y := by
    exact div_le_div_of_nonneg_left hnum hdenpos hdenle
  have hfactorReflect : sixVertexBetheIntegratingFactor c (-x) =
      sixVertexBetheIntegratingFactor c x := by
    simp [sixVertexBetheIntegratingFactor]
  rw [hfactorReflect]
  exact sub_nonneg.mpr hquot

end

end StatMech.FrontierD
