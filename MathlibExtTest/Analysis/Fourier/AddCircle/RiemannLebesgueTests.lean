/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.AddCircle.RiemannLebesgue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tests for the Riemann–Lebesgue lemma on the circle

* The zero function and the constant function `1` have Fourier
  coefficients tending to `0` (the constant function's coefficients are
  `Pi.single 0 1`, so only the `n = 0` coefficient is nonzero).
* A Fourier monomial `fourier m` has coefficients tending to `0`, via
  the continuous version.
* The interval form applies to the zero and constant functions on
  `[0, 1]`.
* The coefficient bound is tight for the constant function `1` at
  `n = 0`: `‖fourierCoeff 1 0‖ = 1 = ∫ ‖1‖`.
-/

namespace MathlibExtTest.Analysis.Fourier.RiemannLebesgueTests

open MeasureTheory Filter Topology
open MathlibExt.Analysis.Fourier.AddCircle.RiemannLebesgue

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The zero function has coefficients tending to `0`. -/
example : Tendsto (fun n : ℤ => fourierCoeff (0 : AddCircle T → ℂ) n)
    cofinite (𝓝 0) :=
  tendsto_fourierCoeff_cofinite
    (integrable_zero (AddCircle T) ℂ (AddCircle.haarAddCircle (T := T)))

/-- The constant function `1` has coefficients tending to `0`. -/
example : Tendsto (fun n : ℤ => fourierCoeff (fun _ : AddCircle T => (1 : ℂ)) n)
    cofinite (𝓝 0) :=
  tendsto_fourierCoeff_cofinite (integrable_const (1 : ℂ))

/-- A Fourier monomial has coefficients tending to `0`. -/
example (m : ℤ) : Tendsto (fun n : ℤ =>
    fourierCoeff ((fourier m : C(AddCircle T, ℂ)) : AddCircle T → ℂ) n)
    cofinite (𝓝 0) :=
  tendsto_fourierCoeff_cofinite_of_continuous (g := fourier m)

/-- Interval form: the zero function on `[0, 1]`. -/
example : Tendsto (fun n : ℤ =>
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun _ => (0 : ℂ)) n)
    cofinite (𝓝 0) :=
  tendsto_fourierCoeffOn_cofinite (by norm_num) IntervalIntegrable.zero

/-- Interval form: the constant function `1` on `[0, 1]`. -/
example : Tendsto (fun n : ℤ =>
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun _ => (1 : ℂ)) n)
    cofinite (𝓝 0) :=
  tendsto_fourierCoeffOn_cofinite (by norm_num) intervalIntegrable_const

/-- The coefficient bound is tight for the constant function `1` at `n = 0`. -/
example : ‖fourierCoeff (fun _ : AddCircle T => (1 : ℂ)) (0 : ℤ)‖ =
    ∫ _ : AddCircle T, ‖(1 : ℂ)‖ ∂(AddCircle.haarAddCircle (T := T)) := by
  have hcoeff : fourierCoeff (fun _ : AddCircle T => (1 : ℂ)) (0 : ℤ) = 1 := by
    have h1 : (fun _ : AddCircle T => (1 : ℂ)) =
        (fourier 0 : AddCircle T → ℂ) := by
      funext x
      simp
    rw [h1]
    exact congr_fun (fourierCoeff_fourier 0) 0
  rw [hcoeff, norm_one]
  simp

end MathlibExtTest.Analysis.Fourier.RiemannLebesgueTests
