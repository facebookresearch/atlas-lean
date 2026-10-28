/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The explicit three-bases spin operator has order dividing three.
Source: Seysen, arXiv:2002.10921v3, Lemma 9.4. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinNormalizer

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

theorem xiGrayGammaProjection_translation (a : XiGrayIndex) :
    xiGrayGammaProjection (xiGrayTranslation (ofAdd a)) = a := by
  unfold xiGrayGammaProjection
  rw [xiGrayTranslation_translation]
  have h : (fun i => spinDot (xiGrayCocodeBasis i) (xiGrayCode a)) = xiGrayDual a := by
    funext i
    rw [xiGrayCode_dot]
    simp only [xiGrayBasis_pairing, xiGrayDual]
  rw [h, xiGrayDual_involutive a]

theorem xiGrayGProjection_modulation (a : XiGrayIndex) :
    xiGrayGProjection (xiGrayModulation (ofAdd a)) = a := by
  unfold xiGrayGProjection
  rw [xiGrayModulation_modulation]
  have h : (fun i => spinDot (xiGrayCocode a) (xiGrayCodeBasis i)) = xiGrayDual a := by
    funext i
    rw [xiGrayCocode_dot]
    simp only [xiGrayBasis_pairing, xiGrayDual, eq_comm]
  rw [h, xiGrayDual_involutive a]

theorem xiGrayBilinear_self (a : XiGrayIndex) : xiGrayBilinear a a = 0 := by
  have h := xiGrayQuadratic_add a a
  have haa : a + a = 0 := by ext i; exact CharTwo.add_self_eq_zero _
  have hzero : xiGrayQuadratic 0 = 0 := by simp [xiGrayQuadratic]
  rw [haa, hzero, CharTwo.add_self_eq_zero, zero_add] at h
  exact h.symm

theorem xiGraySpin_diagonal_commute (a : XiGrayIndex) :
    spinOperator (xiGrayTranslation (ofAdd a)) * spinOperator (xiGrayModulation (ofAdd a)) =
      spinOperator (xiGrayModulation (ofAdd a)) * spinOperator (xiGrayTranslation (ofAdd a)) := by
  simpa only [xiGrayGProjection_modulation, xiGrayBilinear_self, qSign_zero, one_smul] using
    xiGrayTranslation_spin_swap a (xiGrayModulation (ofAdd a))

theorem xiSpinGamma_conjugation_translation (a : XiGrayIndex) :
    xiSpinGamma * spinOperator (xiGrayTranslation (ofAdd a)) * xiSpinGamma =
      qSign (xiGrayQuadratic a) •
        (spinOperator (xiGrayTranslation (ofAdd a)) *
          spinOperator (xiGrayModulation (ofAdd a))) := by
  rw [xiSpinGamma_conjugation, xiSpinGammaImage, xiGrayGammaProjection_translation,
    xiSpinOperator_central_mul]

theorem xiSpinG_conjugation_modulation (a : XiGrayIndex) :
    xiSpinG * spinOperator (xiGrayModulation (ofAdd a)) * xiSpinG =
      qSign (xiGrayQuadratic a) •
        (spinOperator (xiGrayTranslation (ofAdd a)) *
          spinOperator (xiGrayModulation (ofAdd a))) := by
  rw [xiSpinG_conjugation, xiSpinGImage, xiGrayGProjection_modulation,
    xiSpinOperator_central_mul, ← xiGraySpin_diagonal_commute]

theorem xiGrayGaussian_conjugate_sum {A : Type*} [Ring A] [Algebra ℝ A]
    (F : Multiplicative XiGrayIndex →* A) (T : A) :
    T * xiGrayGaussian F * T =
      (1 / 8 : ℝ) • ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) • (T * F (ofAdd a) * T) := by
  simp only [xiGrayGaussian, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]

set_option maxRecDepth 4096 in
/-- The two explicitly constructed Gauss involutions satisfy the braid relation. -/
theorem xiSpin_braid : xiSpinGamma * xiSpinG * xiSpinGamma =
    xiSpinG * xiSpinGamma * xiSpinG := by
  change xiSpinGamma * xiGrayGaussian _ * xiSpinGamma = xiSpinG * xiGrayGaussian _ * xiSpinG
  rw [xiGrayGaussian_conjugate_sum, xiGrayGaussian_conjugate_sum]
  simp only [MonoidHom.comp_apply, xiSpinLinearRepresentation_operator]
  simp only [xiSpinGamma_conjugation_translation, xiSpinG_conjugation_modulation]

/-- The actual column source spin operator satisfies ξ³=1. -/
theorem xiSpinOperator_cube : xiSpinOperator ^ 3 = 1 := by
  unfold xiSpinOperator
  calc
    _ = xiSpinG * (xiSpinGamma * xiSpinG * xiSpinGamma) * xiSpinG * xiSpinGamma := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = xiSpinG * (xiSpinG * xiSpinGamma * xiSpinG) * xiSpinG * xiSpinGamma := by
      rw [xiSpin_braid]
    _ = 1 := by
      calc
        _ = (xiSpinG * xiSpinG) * xiSpinGamma * (xiSpinG * xiSpinG) * xiSpinGamma := by
          simp only [mul_assoc]
        _ = 1 := by rw [xiSpinG_square, one_mul, mul_one, xiSpinGamma_square]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
