/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinHolomorph

/-! Exact sixty-four-term spin coefficients for actual Xi transition words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The integral total of the published six-dimensional quadratic Gauss signs. -/
theorem generatedAxisGlobalXi_sign_sum : (∑ a : XiGrayIndex, xiGraySign a) = -8 := by
  decide +kernel

/-- The real Gauss sign total is minus eight in this source convention. -/
theorem generatedAxisGlobalXi_sign_sum_real :
    (∑ a : XiGrayIndex, qSign (xiGrayQuadratic a)) = (-8 : ℝ) := by
  have h := generatedAxisGlobalXi_sign_sum
  have hr : (↑(∑ a : XiGrayIndex, xiGraySign a) : ℝ) = -8 := by exact_mod_cast h
  simpa only [Int.cast_sum, xiGraySign_real] using hr

/-- The exact source Fourier coefficient of the grey quadratic form. -/
theorem generatedAxisGlobalXi_fourier (p : XiGrayIndex) :
    (∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) =
      -8 * qSign (xiGrayQuadratic p) := by
  simp_rw [xiGraySign_shift]
  rw [← Finset.mul_sum]
  have h := Equiv.sum_comp (Equiv.addRight p) (fun a => qSign (xiGrayQuadratic a))
  change (∑ a : XiGrayIndex, qSign (xiGrayQuadratic (a + p))) =
    ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) at h
  rw [h, generatedAxisGlobalXi_sign_sum_real]
  ring

/-- The six grey Fourier coordinates of an actual physical spin row. -/
def generatedAxisGlobalXiGammaIndex (t : SpinIndex) : XiGrayIndex :=
  xiGrayDual (fun i => spinDot (xiGrayCocodeBasis i) t)

/-- Reading an actual cocode character gives precisely the displayed Fourier coordinates. -/
theorem generatedAxisGlobalXiGammaIndex_pairing (a : XiGrayIndex) (t : SpinIndex) :
    spinDot (xiGrayCocode a) t = xiGrayBilinear a (generatedAxisGlobalXiGammaIndex t) := by
  rw [xiGrayCocode_dot, xiGrayBilinear_dual]
  simp only [generatedAxisGlobalXiGammaIndex]
  rw [xiGrayDual_involutive _]

/-- The actual source cocode Gauss operator is this single signed coordinate multiplier. -/
theorem generatedAxisGlobalXiGamma_apply (f : SpinSpace) (t : SpinIndex) :
    xiSpinGamma f t = -qSign (xiGrayQuadratic (generatedAxisGlobalXiGammaIndex t)) * f t := by
  simp only [xiSpinGamma, xiGrayGaussian, LinearMap.smul_apply, LinearMap.sum_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, MonoidHom.comp_apply,
    xiSpinLinearRepresentation_operator, xiGrayModulation_operator]
  simp_rw [generatedAxisGlobalXiGammaIndex_pairing, ← mul_assoc]
  rw [← Finset.sum_mul, generatedAxisGlobalXi_fourier]
  ring

/-- The actual source translation Gauss operator has exactly sixty-four translated inputs. -/
theorem generatedAxisGlobalXiG_apply (f : SpinSpace) (t : SpinIndex) :
    xiSpinG f t = (1 / 8 : ℝ) *
      ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) * f (t + xiGrayCode a) := by
  simp only [xiSpinG, xiGrayGaussian, LinearMap.smul_apply, LinearMap.sum_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, MonoidHom.comp_apply,
    xiSpinLinearRepresentation_operator, xiGrayTranslation_operator]

/-- The true phase of each of the sixty-four source spin output coefficients. -/
def generatedAxisGlobalXiSpinPhase (a : XiGrayIndex) (t : SpinIndex) : ZMod 2 :=
  xiGrayQuadratic a +
    xiGrayQuadratic (generatedAxisGlobalXiGammaIndex (t + xiGrayCode a)) + 1

/-- The actual source Xi operator uses this exact finite signed sixty-four-term formula. -/
theorem generatedAxisGlobalXiSpin_apply (f : SpinSpace) (t : SpinIndex) :
    8 * xiSpinOperator f t =
      ∑ a : XiGrayIndex, qSign (generatedAxisGlobalXiSpinPhase a t) *
        f (t + xiGrayCode a) := by
  change 8 * xiSpinG (xiSpinGamma f) t = _
  rw [generatedAxisGlobalXiG_apply]
  simp_rw [generatedAxisGlobalXiGamma_apply, generatedAxisGlobalXiSpinPhase,
    qSign_add, qSign_one]
  simp only [mul_neg, ← mul_assoc]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
