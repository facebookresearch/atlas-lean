/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Tests for Fourier coefficients of `C¹` periodic functions

* `x ↦ (Real.cos x : ℂ)` on a `2π` period: summable coefficients, uniform
  convergence of the Fourier series, pointwise convergence at `π / 2`, the
  decay rate `n · ‖ĉₙ‖ → 0`, and the numeric bound `‖ĉ₃(cos)‖ ≤ 1 / 3` from
  the coefficient identity plus `‖ĉ₃(-sin)‖ ≤ 1`.
* `x ↦ (Real.sin (2 * x) : ℂ)` on a `π` period: summable coefficients.
-/

namespace MathlibExtTest.Analysis.Fourier.C1FourierSummableTests

open MeasureTheory Filter Topology
open MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable

theorem cos_periodic_complex :
    Function.Periodic (fun x => (Real.cos x : ℂ)) (2 * Real.pi) := by
  intro y
  exact congrArg _ (Real.cos_periodic y)

theorem cos_hasDerivAt_complex (x : ℝ) :
    HasDerivAt (fun y => (Real.cos y : ℂ)) (-(Real.sin x : ℂ)) x := by
  simpa using (Real.hasDerivAt_cos x).ofReal_comp

theorem cos_continuous_complex : Continuous (fun x => (Real.cos x : ℂ)) :=
  Complex.continuous_ofReal.comp Real.continuous_cos

theorem neg_sin_continuous_complex : Continuous (fun x => -(Real.sin x : ℂ)) :=
  (Complex.continuous_ofReal.comp Real.continuous_sin).neg

theorem sin_two_periodic_complex :
    Function.Periodic (fun x => (Real.sin (2 * x) : ℂ)) Real.pi := by
  intro y
  show (Real.sin (2 * (y + Real.pi)) : ℂ) = (Real.sin (2 * y) : ℂ)
  have h : 2 * (y + Real.pi) = 2 * y + 2 * Real.pi := by ring
  rw [h]
  exact congrArg _ (Real.sin_add_two_pi (2 * y))

theorem sin_two_hasDerivAt_complex (x : ℝ) :
    HasDerivAt (fun y => (Real.sin (2 * y) : ℂ))
      ((Real.cos (2 * x) * 2 : ℝ) : ℂ) x := by
  have h : HasDerivAt (fun y => Real.sin (2 * y)) (Real.cos (2 * x) * 2) x := by
    simpa using ((hasDerivAt_id x).const_mul 2).sin
  simpa using h.ofReal_comp

theorem sin_two_deriv_continuous_complex :
    Continuous (fun x => ((Real.cos (2 * x) * 2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (by fun_prop)

/-- The cosine function has summable Fourier coefficients on a `2π` period. -/
theorem cos_summable_fourierCoeffOn (hT : (0:ℝ) < 2 * Real.pi) :
    Summable (fourierCoeffOn hT (fun x => (Real.cos x : ℂ))) :=
  summable_fourierCoeffOn_of_hasDerivAt hT cos_periodic_complex
    (fun x => cos_hasDerivAt_complex x) neg_sin_continuous_complex

/-- The cosine function has summable Fourier coefficients, with the period
written out (no separate `hT` hypothesis). -/
example : Summable (fourierCoeffOn (show (0:ℝ) < 2 * Real.pi by positivity)
    (fun x => (Real.cos x : ℂ))) :=
  cos_summable_fourierCoeffOn (by positivity)

/-- `x ↦ sin (2x)` has summable Fourier coefficients on a `π` period. -/
theorem sin_two_mul_summable_fourierCoeffOn (hT : (0:ℝ) < Real.pi) :
    Summable (fourierCoeffOn hT (fun x => (Real.sin (2 * x) : ℂ))) :=
  summable_fourierCoeffOn_of_hasDerivAt hT sin_two_periodic_complex
    (fun x => sin_two_hasDerivAt_complex x) sin_two_deriv_continuous_complex

/-- The Fourier series of `cos` converges uniformly on the circle. -/
theorem cos_hasSum_fourier_series (hT : (0:ℝ) < 2 * Real.pi) [hT' : Fact (0 < 2 * Real.pi)] :
    HasSum (fun n : ℤ => fourierCoeffOn hT (fun x => (Real.cos x : ℂ)) n •
        (fourier n : C(AddCircle (2 * Real.pi), ℂ)))
      (liftPeriodicContinuousMap cos_periodic_complex cos_continuous_complex) :=
  hasSum_fourier_series_of_hasDerivAt hT cos_periodic_complex cos_continuous_complex
    (fun x => cos_hasDerivAt_complex x) neg_sin_continuous_complex

/-- The Fourier series of `cos` converges pointwise at `π / 2`. -/
theorem cos_hasSum_fourier_series_apply (hT : (0:ℝ) < 2 * Real.pi)
    [hT' : Fact (0 < 2 * Real.pi)] :
    HasSum (fun n : ℤ => fourierCoeffOn hT (fun x => (Real.cos x : ℂ)) n •
        (fourier n ((Real.pi / 2 : ℝ) : AddCircle (2 * Real.pi)) : ℂ))
      (Real.cos (Real.pi / 2) : ℂ) := by
  refine hasSum_fourier_series_of_hasDerivAt_apply hT cos_periodic_complex
    cos_continuous_complex (fun x => cos_hasDerivAt_complex x)
    neg_sin_continuous_complex ?_
  exact Set.mem_Ioc.mpr ⟨by positivity, by linarith [Real.pi_pos]⟩

/-- Decay rate for `cos`: `n · ‖ĉₙ(cos)‖ → 0`. -/
theorem cos_tendsto_mul_norm_fourierCoeffOn (hT : (0:ℝ) < 2 * Real.pi) :
    Filter.Tendsto (fun n : ℤ => (n : ℝ) * ‖fourierCoeffOn hT (fun x => (Real.cos x : ℂ)) n‖)
      Filter.cofinite (nhds 0) :=
  tendsto_mul_norm_fourierCoeffOn_of_hasDerivAt hT cos_periodic_complex
    (fun x => cos_hasDerivAt_complex x) neg_sin_continuous_complex

/-- Numeric coefficient bound: `‖ĉ₃(cos)‖ ≤ 1 / 3`. -/
theorem cos_fourierCoeff_three_le (hT : (0:ℝ) < 2 * Real.pi) :
    ‖fourierCoeffOn hT (fun x => (Real.cos x : ℂ)) 3‖ ≤ 1 / 3 := by
  have hf' : IntervalIntegrable (fun x => -(Real.sin x : ℂ)) volume 0 (2 * Real.pi) :=
    neg_sin_continuous_complex.intervalIntegrable 0 (2 * Real.pi)
  have hnorm := norm_fourierCoeffOn_eq_of_hasDerivAt hT cos_periodic_complex
    (fun x => cos_hasDerivAt_complex x) hf' (n := 3) (by norm_num)
  have h3 : |((3 : ℤ) : ℝ)| = 3 := by norm_num
  rw [h3] at hnorm
  rw [hnorm]
  have hbound : ‖fourierCoeffOn hT (fun x => -(Real.sin x : ℂ)) 3‖ ≤ 1 := by
    have hC : ∀ x ∈ Set.Icc (0:ℝ) (2 * Real.pi), ‖(-(Real.sin x : ℂ))‖ ≤ 1 := by
      intro x _
      have h1 : ‖(-(Real.sin x : ℂ))‖ = |Real.sin x| := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
      rw [h1]
      exact Real.abs_sin_le_one x
    have h := norm_fourierCoeffOn_le_of_bound hT hC 3
    simpa using h
  calc (2 * Real.pi / (2 * Real.pi * 3)) *
        ‖fourierCoeffOn hT (fun x => -(Real.sin x : ℂ)) 3‖
      ≤ (2 * Real.pi / (2 * Real.pi * 3)) * 1 :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 1 / 3 := by
        rw [mul_one, div_eq_iff (by positivity : (2 * Real.pi * 3 : ℝ) ≠ 0)]
        ring

end MathlibExtTest.Analysis.Fourier.C1FourierSummableTests

namespace MathlibExtTest.Analysis.Fourier.C1FourierSummableTests

open MeasureTheory Filter Topology

/-- The decay API controls the coefficient magnitude at both positive and negative frequencies. -/
theorem cos_tendsto_abs_mul_norm_fourierCoeffOn (hT : (0 : ℝ) < 2 * Real.pi) :
    Filter.Tendsto (fun n : ℤ => |(n : ℝ)| *
      ‖fourierCoeffOn hT (fun x => (Real.cos x : ℂ)) n‖)
      Filter.cofinite (nhds 0) := by
  have h := (cos_tendsto_mul_norm_fourierCoeffOn hT).norm
  simpa only [norm_mul, Real.norm_eq_abs, abs_norm, norm_zero] using h

end MathlibExtTest.Analysis.Fourier.C1FourierSummableTests
