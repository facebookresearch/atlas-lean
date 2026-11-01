/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinLeechCompatibility

/-! Coordinate formulas for the genuine grey Gauss factors used in the fourth-axis lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual grey quadratic signs have the exact negative Gauss sum. -/
theorem generatedFourth_grey_gauss_certificate :
    (∑ a : XiGrayIndex, xiGraySign a) = -8 := by decide +kernel

/-- The exact Fourier coefficient follows by completing the actual quadratic square. -/
theorem generatedFourth_grey_fourier (p : XiGrayIndex) :
    (∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) =
      -8 * qSign (xiGrayQuadratic p) := by
  have hsum : (∑ a : XiGrayIndex, qSign (xiGrayQuadratic a)) = -8 := by
    simp_rw [← xiGraySign_real]
    exact_mod_cast generatedFourth_grey_gauss_certificate
  have hp (a : XiGrayIndex) :
      qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p) =
        qSign (xiGrayQuadratic p) * qSign (xiGrayQuadratic (a + p)) := by
    rw [xiGrayQuadratic_add, qSign_add, qSign_add]
    have hs := qSign_sq (xiGrayQuadratic p)
    calc
      _ = (qSign (xiGrayQuadratic p) * qSign (xiGrayQuadratic p)) *
        (qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) := by rw [hs, one_mul]
      _ = _ := by ring
  simp_rw [hp]
  rw [← Finset.mul_sum]
  have he : (∑ a : XiGrayIndex, qSign (xiGrayQuadratic (a + p))) =
      ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) := by
    exact Equiv.sum_comp (Equiv.addRight p) (fun a : XiGrayIndex => qSign (xiGrayQuadratic a))
  rw [he, hsum]
  ring

/-- The genuine translation Gauss factor is its explicit 64-shift coordinate sum. -/
theorem generatedFourth_xi_g_apply (f : SpinSpace) (t : SpinIndex) :
    xiSpinG f t = (1 / 8 : ℝ) * ∑ a : XiGrayIndex,
      qSign (xiGrayQuadratic a) * f (t + xiGrayCode a) := by
  simp only [xiSpinG, xiGrayGaussian, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    MonoidHom.comp_apply, xiSpinLinearRepresentation_operator, xiGrayTranslation_operator,
    Pi.smul_apply, smul_eq_mul]

/-- The cocode Gauss factor is the exact diagonal quadratic sign. -/
theorem generatedFourth_xi_gamma_apply (f : SpinSpace) (t : SpinIndex) :
    xiSpinGamma f t = -qSign (xiGrayQuadratic
      (xiGrayDual (fun i => spinDot (xiGrayCocodeBasis i) t))) * f t := by
  let q : Q := ⟨ofAdd (Fin.append t (0 : SpinIndex)), 1⟩
  have ht : spinTranslation q = t := by
    ext i
    exact Fin.append_left _ _ i
  have hp (a : XiGrayIndex) : spinDot (xiGrayCocode a) t =
      xiGrayBilinear a (xiGrayDual (fun i => spinDot (xiGrayCocodeBasis i) t)) := by
    have h := xiGrayGammaProjection_pairing a q
    simpa only [xiGrayGammaProjection, ht] using h
  simp only [xiSpinGamma, xiGrayGaussian, LinearMap.smul_apply, LinearMap.sum_apply,
    Finset.sum_apply,
    MonoidHom.comp_apply, xiSpinLinearRepresentation_operator,
    xiGrayModulation_operator,
    Pi.smul_apply, smul_eq_mul, hp]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, generatedFourth_grey_fourier]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
