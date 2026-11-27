/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The Laplace distribution

The Laplace distribution with location `m` and scale `b > 0` has Lebesgue density
`exp (-|z - m| / b) / (2 b)` (Dwork and Roth, *The Algorithmic Foundations of Differential
Privacy*, 2014, Definition 3.2). It is the noise distribution of the Laplace mechanism of
differential privacy (`CSLibExt.Crypto.Privacy.Laplace`).

## Main results

* `ProbabilityTheory.laplacePDFReal`, `ProbabilityTheory.laplaceMeasure`: the density and the law.
* `ProbabilityTheory.integral_laplacePDFReal`,
  `ProbabilityTheory.isProbabilityMeasure_laplaceMeasure`: the density integrates to `1`.
* `ProbabilityTheory.laplacePDFReal_le_exp_mul`, `ProbabilityTheory.laplaceMeasure_le_smul`:
  moving the location by `a` changes the density, and the law, by a factor at most
  `exp (|a| / b)`.

`Cslib.MachineLearning.LeastSquares.laplacePDF b` (module
`CSLibExt.MachineLearning.Regression.LeastSquares`) is the centred density with the
scale in `ℝ≥0`; for `b > 0` it equals `laplacePDFReal 0 b`.
-/

@[expose] public section

open MeasureTheory Set Real
open scoped ENNReal

namespace ProbabilityTheory

/-- **Density of the Laplace distribution.** The Laplace distribution with location `m` and scale
`b` has density `z ↦ exp (-|z - m| / b) / (2 b)` (Dwork and Roth, *The Algorithmic Foundations of
Differential Privacy*, 2014, Definition 3.2, there centred at `0`; the symmetric version of the
exponential law). -/
noncomputable def laplacePDFReal (m b z : ℝ) : ℝ :=
  Real.exp (-|z - m| / b) / (2 * b)

/-- **Laplace distribution.** The measure on `ℝ` with density `laplacePDFReal m b` with respect
to Lebesgue measure (Dwork and Roth, 2014, Definition 3.2). It is a probability measure for a
positive scale `b > 0` (`isProbabilityMeasure_laplaceMeasure`). Like Mathlib's exponential and
gamma measures it is defined for every `b`: for `b ≤ 0` the density is never positive (at `b = 0`
it is `0` by `x / 0 = 0`), so the measure is zero. -/
noncomputable def laplaceMeasure (m b : ℝ) : Measure ℝ :=
  volume.withDensity fun z ↦ ENNReal.ofReal (laplacePDFReal m b z)

instance (m b : ℝ) : SFinite (laplaceMeasure m b) := by
  unfold laplaceMeasure
  infer_instance

theorem laplacePDFReal_nonneg {b : ℝ} (hb : 0 < b) (m z : ℝ) : 0 ≤ laplacePDFReal m b z :=
  div_nonneg (Real.exp_pos _).le (by positivity)

theorem measurable_laplacePDFReal (m b : ℝ) : Measurable (laplacePDFReal m b) := by
  unfold laplacePDFReal
  fun_prop

/-- **The Laplace density integrates to one.** For `b > 0`,
`∫ exp (-|z - m| / b) / (2 b) dz = 1`, so `laplaceMeasure m b` is a probability measure
(Dwork and Roth, 2014, Definition 3.2). -/
theorem integral_laplacePDFReal {b : ℝ} (hb : 0 < b) (m : ℝ) :
    ∫ z, laplacePDFReal m b z = 1 := by
  have h1 : ∫ z, laplacePDFReal m b z = ∫ z, laplacePDFReal 0 b z := by
    simpa [laplacePDFReal] using
      integral_sub_right_eq_self (μ := volume) (fun z ↦ laplacePDFReal 0 b z) m
  rw [h1]
  have h2 : ∫ z, laplacePDFReal 0 b z = ∫ z, (fun t ↦ Real.exp ((-1 / b) * t) / (2 * b)) |z| := by
    congr 1
    funext z
    simp only [laplacePDFReal, sub_zero]
    ring_nf
  rw [h2, integral_comp_abs (f := fun t ↦ Real.exp ((-1 / b) * t) / (2 * b)),
    integral_div, integral_exp_mul_Ioi (by
    have := one_div_pos.mpr hb
    linarith [show -1 / b = -(1 / b) by ring]) 0]
  field_simp
  simp

/-- **The Laplace law is a probability measure.** For `b > 0`, `laplaceMeasure m b` has total
mass `1` (Dwork and Roth, 2014, Definition 3.2). -/
theorem isProbabilityMeasure_laplaceMeasure {b : ℝ} (hb : 0 < b) (m : ℝ) :
    IsProbabilityMeasure (laplaceMeasure m b) := by
  constructor
  have hint : Integrable (laplacePDFReal m b) :=
    Integrable.of_integral_ne_zero (by rw [integral_laplacePDFReal hb]; exact one_ne_zero)
  rw [laplaceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (laplacePDFReal_nonneg hb m)),
    integral_laplacePDFReal hb, ENNReal.ofReal_one]

/-- **Shifting the Laplace density.** Moving the location from `m'` to `m` multiplies the density
by at most `exp (|m - m'| / b)`: `laplacePDFReal m b z ≤ exp (|m - m'| / b) · laplacePDFReal m' b z`
(the pointwise bound in the proof of Dwork and Roth, 2014, Theorem 3.6). -/
theorem laplacePDFReal_le_exp_mul {b : ℝ} (hb : 0 < b) (m m' z : ℝ) :
    laplacePDFReal m b z ≤ Real.exp (|m - m'| / b) * laplacePDFReal m' b z := by
  unfold laplacePDFReal
  rw [← mul_div_assoc, ← Real.exp_add]
  gcongr
  rw [← add_div, div_le_div_iff_of_pos_right hb]
  have := abs_sub_le z m m'
  linarith

/-- **Laplace laws at nearby locations.** For `b > 0`,
`laplaceMeasure m b ≤ exp (|m - m'| / b) • laplaceMeasure m' b` as measures (integrated form of the
pointwise bound in the proof of Dwork and Roth, 2014, Theorem 3.6). -/
theorem laplaceMeasure_le_smul {b : ℝ} (hb : 0 < b) (m m' : ℝ) :
    laplaceMeasure m b ≤ ENNReal.ofReal (Real.exp (|m - m'| / b)) • laplaceMeasure m' b := by
  rw [Measure.le_iff]
  intro S hS
  simp only [laplaceMeasure]
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hS,
    withDensity_apply _ hS, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z ↦ ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (laplacePDFReal_le_exp_mul hb m m' z)

end ProbabilityTheory
