/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinHolomorph

/-! The original Gaussian Q-image phase uses its two genuine six-coordinate projections. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original off-diagonal grey dual is additive. -/
theorem generatedSixth_xi_gray_dual_add (a b : XiGrayIndex) :
    xiGrayDual (a + b) = xiGrayDual a + xiGrayDual b := by
  ext i
  simp only [xiGrayDual, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The actual diagonal Gaussian image adds precisely its grey cocode projection. -/
theorem generatedSixth_xi_gamma_modulation (q : Q) :
    spinModulation (xiSpinGammaImage q) =
      spinModulation q + xiGrayCocode (xiGrayGammaProjection q) := by
  rw [xiSpinGammaImage, spinModulation_mul, spinModulation_mul, xiGrayModulation_modulation]
  change (0 + spinModulation q) + _ = _
  rw [zero_add]

/-- The alternating self-pairing cancels exactly in the original diagonal Gaussian phase. -/
theorem generatedSixth_xi_gamma_coefficient (q : Q) :
    toAdd (xiSpinGammaImage q).coeff =
      xiGrayQuadratic (xiGrayGammaProjection q) + toAdd q.coeff := by
  rw [xiSpinGammaImage, mul_assoc, qCentral_mul_coeff]
  change xiGrayQuadratic (xiGrayGammaProjection q) +
    (toAdd q.coeff + 0 + qBeta (toAdd q.base)
      (binaryCocodeEmbedding (xiGrayCocode (xiGrayGammaProjection q)))) = _
  have hb : qBeta (toAdd q.base)
      (binaryCocodeEmbedding (xiGrayCocode (xiGrayGammaProjection q))) =
      spinDot (xiGrayCocode (xiGrayGammaProjection q)) (spinTranslation q) := by
    simp only [qBeta, binaryCocodeEmbedding_right, spinDot, spinTranslation, mul_comm]
  rw [hb, xiGrayGammaProjection_pairing, xiGrayBilinear_self, add_zero, add_zero]

/-- A right grey translation contributes its actual quadratic and no extra cocycle term. -/
theorem generatedSixth_xi_g_coefficient (q : Q) :
    toAdd (xiSpinGImage q).coeff = xiGrayQuadratic (xiGrayGProjection q) + toAdd q.coeff := by
  rw [xiSpinGImage, mul_assoc, qCentral_mul_coeff]
  change xiGrayQuadratic (xiGrayGProjection q) +
    (toAdd q.coeff + 0 + qBeta (toAdd q.base)
      (Fin.append (xiGrayCode (xiGrayGProjection q)) (0 : SpinIndex))) = _
  simp only [qBeta, Fin.append_right, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]

/-- The second genuine grey projection is the original cocode projection plus the first one. -/
theorem generatedSixth_xi_gamma_g_projection (q : Q) :
    xiGrayGProjection (xiSpinGammaImage q) = xiGrayGProjection q + xiGrayGammaProjection q := by
  have hf : (fun i => spinDot
      (spinModulation q + xiGrayCocode (xiGrayGammaProjection q)) (xiGrayCodeBasis i)) =
      (fun i => spinDot (spinModulation q) (xiGrayCodeBasis i)) +
        xiGrayDual (xiGrayGammaProjection q) := by
    funext i
    rw [spinDot_add_left, xiGrayCocode_dot]
    simp only [Pi.add_apply, xiGrayDual, xiGrayBasis_pairing]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [eq_comm]
  unfold xiGrayGProjection
  rw [generatedSixth_xi_gamma_modulation, hf, generatedSixth_xi_gray_dual_add,
    xiGrayDual_involutive]

/-- The full original Xi Q-image retains the central sign and two actual grey quadratics. -/
theorem generatedSixth_xi_gaussian_coefficient (q : Q) :
    toAdd (xiSpinGImage (xiSpinGammaImage q)).coeff =
      toAdd q.coeff + xiGrayQuadratic (xiGrayGammaProjection q) +
        xiGrayQuadratic (xiGrayGammaProjection q + xiGrayGProjection q) := by
  rw [generatedSixth_xi_g_coefficient, generatedSixth_xi_gamma_g_projection,
    generatedSixth_xi_gamma_coefficient,
    add_comm (xiGrayGProjection q) (xiGrayGammaProjection q)]
  ring

/-- This is the coefficient of the genuine source Xi spin conjugation on every Q element. -/
theorem generatedSixth_xi_conjugation_coefficient (q : Q) :
    toAdd (spinConjugation xiSpinHolomorph q).coeff =
      toAdd q.coeff + xiGrayQuadratic (xiGrayGammaProjection q) +
        xiGrayQuadratic (xiGrayGammaProjection q + xiGrayGProjection q) := by
  rw [xiSpinHolomorph_conjugation, generatedSixth_xi_gaussian_coefficient]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
