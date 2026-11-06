/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integral diagonal and 64-term numerators for the actual three-bases spin factor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Verify the Fourier transform on all 64 characters of the six-dimensional grey space.
/-- The exact integral Fourier transform of the published nonsingular quadratic signs. -/
theorem nortonUIntegerGamma_fourier : ∀ b : XiGrayIndex,
    (∑ a : XiGrayIndex, xiGraySign a * nortonUIntegerSign (∑ i, a i * b i)) =
      -8 * nortonUIntegerSign (xiGrayQuadratic (xiGrayDual b)) := by
  decide +kernel

/-- The six actual cocode characters evaluated at a spin coordinate. -/
def nortonUIntegerGammaCharacters (t : SpinIndex) : XiGrayIndex :=
  fun i => spinDot (xiGrayCocodeBasis i) t

/-- The actual first Gaussian is an integral diagonal sign after Fourier evaluation. -/
def nortonUIntegerGammaSign (t : SpinIndex) : ℤ :=
  -nortonUIntegerSign (xiGrayQuadratic (xiGrayDual (nortonUIntegerGammaCharacters t)))

/-- The Gaussian coefficient at every actual spin coordinate is eight times this sign. -/
theorem nortonUIntegerGamma_coefficient (t : SpinIndex) :
    (∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) * qSign (spinDot (xiGrayCocode a) t)) =
      8 * (nortonUIntegerGammaSign t : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (nortonUIntegerGamma_fourier (nortonUIntegerGammaCharacters t))
  simp only [Int.cast_sum, Int.cast_mul, xiGraySign_real, nortonUIntegerSign_real,
    Int.cast_neg, Int.cast_ofNat] at h
  simp only [xiGrayCocode_dot]
  simp only [nortonUIntegerGammaSign, Int.cast_neg, nortonUIntegerSign_real]
  simp only [nortonUIntegerGammaCharacters] at h ⊢
  rw [h]
  ring

/-- The exact cocode Gaussian acts by the computed integral diagonal sign. -/
theorem nortonUIntegerGamma_apply (f : SpinSpace) (t : SpinIndex) :
    xiSpinGamma f t = (nortonUIntegerGammaSign t : ℝ) * f t := by
  simp only [xiSpinGamma, xiGrayGaussian, LinearMap.smul_apply, LinearMap.sum_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, MonoidHom.comp_apply]
  change (1 / 8 : ℝ) * ∑ a : XiGrayIndex,
    qSign (xiGrayQuadratic a) * spinOperator (xiGrayModulation (ofAdd a)) f t = _
  simp only [xiGrayModulation_operator, ← mul_assoc, ← Finset.sum_mul]
  rw [nortonUIntegerGamma_coefficient]
  ring

/-- The other Gaussian has the source's actual 64-term translation formula. -/
theorem nortonUIntegerG_apply (f : SpinSpace) (t : SpinIndex) :
    xiSpinG f t = (1 / 8 : ℝ) *
      ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) * f (t + xiGrayCode a) := by
  simp only [xiSpinG, xiGrayGaussian, LinearMap.smul_apply, LinearMap.sum_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, MonoidHom.comp_apply]
  change (1 / 8 : ℝ) * ∑ a : XiGrayIndex,
    qSign (xiGrayQuadratic a) * spinOperator (xiGrayTranslation (ofAdd a)) f t = _
  simp only [xiGrayTranslation_operator]

/-- The integral diagonal operation corresponding to the exact first Gaussian. -/
def nortonUIntegerGamma (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => nortonUIntegerGammaSign (golayLabelCoefficients n) * v n

/-- Its integer embedding is the actual cocode Gaussian with no remaining denominator. -/
theorem nortonUIntegerGamma_embed (v : NortonUIntegerVector) :
    xiSpinGamma (nortonUIntegerEmbed v) = nortonUIntegerEmbed (nortonUIntegerGamma v) := by
  ext t
  simp only [nortonUIntegerGamma_apply, nortonUIntegerEmbed, nortonUIntegerGamma,
    nortonUIntegerLabel_inverse, Int.cast_mul]

/-- The integral 64-term numerator of the source translation Gaussian. -/
def nortonUIntegerG (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => ∑ a : XiGrayIndex, xiGraySign a *
    v (nortonUIntegerLabel (golayLabelCoefficients n + xiGrayCode a))

/-- Dividing its exact integer numerator by eight gives the actual translation Gaussian. -/
theorem nortonUIntegerG_embed (v : NortonUIntegerVector) :
    xiSpinG (nortonUIntegerEmbed v) =
      (1 / 8 : ℝ) • nortonUIntegerEmbed (nortonUIntegerG v) := by
  ext t
  simp only [nortonUIntegerG_apply, nortonUIntegerEmbed, nortonUIntegerG,
    nortonUIntegerLabel_inverse, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul, xiGraySign_real]

/-- One exact integer three-bases numerator: diagonal first, then the 64 translations. -/
def nortonUIntegerXi (v : NortonUIntegerVector) : NortonUIntegerVector :=
  nortonUIntegerG (nortonUIntegerGamma v)

/-- The integer numerator is precisely eight times the actual source spin factor. -/
theorem nortonUIntegerXi_embed (v : NortonUIntegerVector) :
    xiSpinHolomorph.val (nortonUIntegerEmbed v) =
      (1 / 8 : ℝ) • nortonUIntegerEmbed (nortonUIntegerXi v) := by
  change xiSpinG (xiSpinGamma (nortonUIntegerEmbed v)) = _
  rw [nortonUIntegerGamma_embed, nortonUIntegerG_embed]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
