/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.Integral
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Actual bounded spectral imaginary-power coordinates

The bounded Borel coordinate is exp(it log r). On the positive real spectrum
this is the original r^(it). The total real-log convention is immaterial to
a positive nonsingular operator's spectral measure, which assigns zero to
the nonpositive excluded spectrum. The coordinate has modulus one at every
real r and is integrated using the existing strict bounded PVM integral.

These are actual coordinate/operator DATA from a given spectral measure.
No source Delta, spectral resolution, polar decomposition or unitary family
is selected from an open theorem. Positivity, nonsingularity and the link to
a given original operator are retained in the later whole source statement.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.Analysis.InnerProductSpace
namespace ProjectionValuedMeasure

noncomputable section

open _root_.MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure

/-- The actual bounded measurable exp(it log r) coordinate on the real spectral axis. -/
def imaginaryPowerCoordinate (t : ℝ) : BoundedMeasurableFunction ℝ := by
  refine ⟨⟨(show PreLp (fun _ : ℝ => ℂ) from
    fun r => Complex.exp (((t : ℂ) * Complex.I) * (Real.log r : ℂ))), ?_⟩, ?_⟩
  · change Memℓp (fun r : ℝ => Complex.exp (((t : ℂ) * Complex.I) * (Real.log r : ℂ))) (⊤ : ℝ≥0∞)
    rw [memℓp_infty_iff]
    refine ⟨1, ?_⟩
    rintro _ ⟨r, rfl⟩
    change ‖Complex.exp (((t : ℂ) * Complex.I) * (Real.log r : ℂ))‖ ≤ 1
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  · change Measurable fun r : ℝ => Complex.exp (((t : ℂ) * Complex.I) * (Real.log r : ℂ))
    exact Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp Real.measurable_log))

/-- The coordinate retains its exact original positive-spectral exponential/logarithm value. -/
@[simp]
theorem imaginaryPowerCoordinate_apply (t r : ℝ) :
    imaginaryPowerCoordinate t r = Complex.exp (((t : ℂ) * Complex.I) * (Real.log r : ℂ)) :=
  rfl

/-- The actual imaginary-power coordinate has modulus one on the whole real axis. -/
theorem imaginaryPowerCoordinate_norm (t r : ℝ) : ‖imaginaryPowerCoordinate t r‖ = 1 := by
  rw [imaginaryPowerCoordinate_apply, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual bounded spectral integral of the original imaginary-power coordinate. -/
def spectralImaginaryPower (E : ProjectionValuedMeasure ℝ H) (t : ℝ) : H →L[ℂ] H :=
  E.spectralIntegral (imaginaryPowerCoordinate t)

/-- Every coefficient of the actual power is the original spectral coefficient integral. -/
theorem spectralImaginaryPower_inner (E : ProjectionValuedMeasure ℝ H) (t : ℝ) (g h : H) :
    inner ℂ h (spectralImaginaryPower E t g) = complexIntegral (E.scalarMeasure g h) (imaginaryPowerCoordinate t) :=
  inner_spectralIntegral_apply E (imaginaryPowerCoordinate t) g h

end

end ProjectionValuedMeasure
end MathlibExt.Analysis.InnerProductSpace
