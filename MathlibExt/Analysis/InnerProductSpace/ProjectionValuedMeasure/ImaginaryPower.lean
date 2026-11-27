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
# Bounded imaginary-power functions and spectral integrals

For `t : ℝ`, the measurable bounded function on the real axis is `f_t(r)=exp(i t log r)`, using
the total real logarithm. It has modulus one at every real `r`; on `r>0` it is the imaginary
power `r^(it)`.

For a projection-valued measure `E` on `ℝ` acting on a complete complex Hilbert space `H`,
define `S_t=∫ f_t dE`. Its coefficients are `⟨h,S_t g⟩=∫ exp(i t log r) dμ_(g,h)(r)`, where
`μ_(g,h)(s)=⟨h,E(s)g⟩`. Countable additivity of `E` is in the strong operator topology. The
definition uses any such PVM, without assuming a separately given positive or nonsingular
operator.

The total logarithm satisfies `Real.log 0=0` and `Real.log r=Real.log |r|` for `r<0`. Hence
`f_t(0)=1`, while negative arguments have multiplier `exp(i t log |r|)`. A PVM concentrated at
zero therefore has `S_t=I_H`.
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

/-- **Bounded imaginary-power coordinate on the real axis.** For `t : ℝ`,
`imaginaryPowerCoordinate t : BoundedMeasurableFunction ℝ` has value `r ↦ exp(i t log r)`
and supremum norm one. The real logarithm is total, with `log 0=0`; for `r>0` the value is
`r^(it)`.

The total real logarithm satisfies `Real.log 0=0` and `Real.log r=Real.log |r|` for `r<0`.
The multiplier is therefore 1 at zero and `exp(i t log |r|)` at negative arguments. -/
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

/-- **Value of the spectral imaginary-power coordinate.** For all `t,r : ℝ`,
`imaginaryPowerCoordinate t r = exp(((t : ℂ)*i)*(Real.log r : ℂ))`. On positive `r`, this
is `r^(it)`.

At `r=0`, the multiplier is `exp(0)=1`. At `r<0`, `Real.log r=Real.log |r|`, so the value
is `exp(i t log |r|)`. -/
@[simp]
theorem imaginaryPowerCoordinate_apply (t r : ℝ) :
    imaginaryPowerCoordinate t r = Complex.exp (((t : ℂ) * Complex.I) * (Real.log r : ℂ)) :=
  rfl

/-- **Modulus of the imaginary-power coordinate.** For every `t,r : ℝ`,
`‖imaginaryPowerCoordinate t r‖=1`, including `r=0` and negative `r`, since the
exponential has purely imaginary exponent.

The total logarithm satisfies `Real.log 0=0`, giving multiplier 1 at zero, and `Real.log
r=Real.log |r|` at negative arguments. -/
theorem imaginaryPowerCoordinate_norm (t r : ℝ) : ‖imaginaryPowerCoordinate t r‖ = 1 := by
  rw [imaginaryPowerCoordinate_apply, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Spectral integral of an imaginary-power function.** Let `H` be a complete complex
Hilbert space and `E : ProjectionValuedMeasure ℝ H` a strongly countably additive PVM. For
`t : ℝ`, `spectralImaginaryPower E t : H →L[ℂ] H` is the bounded operator `S_t=∫ exp(i t
log r) dE(r)`.

The total real logarithm gives `f_t(0)=1` and `f_t(r)=exp(i t log |r|)` for `r<0`. A PVM
concentrated at zero therefore gives `S_t=I_H`. -/
def spectralImaginaryPower (E : ProjectionValuedMeasure ℝ H) (t : ℝ) : H →L[ℂ] H :=
  E.spectralIntegral (imaginaryPowerCoordinate t)

/-- **Coefficient integral of a spectral imaginary power.** Let `H` be a complete complex
Hilbert space, `E : ProjectionValuedMeasure ℝ H` a strongly countably additive PVM, `t :
ℝ`, and `g,h ∈ H`. Then `⟨h,spectralImaginaryPower E t g⟩ = ∫ exp(i t log r) dμ_(g,h)(r)`,
where the finite complex measure is `μ_(g,h)(s)=⟨h,E(s)g⟩`. The inner product is linear in
its second argument.

In this coefficient integral the multiplier is 1 at `r=0`. For `r<0`, `Real.log r=Real.log
|r|`, so the integrand is `exp(i t log |r|)`. If `E` is concentrated at zero,
`spectralImaginaryPower E t=I_H` and this coefficient is `⟨h,g⟩`. -/
theorem spectralImaginaryPower_inner (E : ProjectionValuedMeasure ℝ H) (t : ℝ) (g h : H) :
    inner ℂ h (spectralImaginaryPower E t g) = complexIntegral (E.scalarMeasure g h) (imaginaryPowerCoordinate t) :=
  inner_spectralIntegral_apply E (imaginaryPowerCoordinate t) g h

end

end ProjectionValuedMeasure
end MathlibExt.Analysis.InnerProductSpace
