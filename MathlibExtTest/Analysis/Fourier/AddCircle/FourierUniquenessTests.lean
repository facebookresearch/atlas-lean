/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.AddCircle.FourierUniqueness
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tests for Fourier-coefficient uniqueness

* The zero function has vanishing coefficients, and uniqueness recovers `0`.
* The constant function `1` is the unique continuous function whose only
  nonzero Fourier coefficient is `ĉ₀ = 1` (the `Pi.single 0 1` sequence):
  this exercises `eq_of_fourierCoeff_eq` against Mathlib's
  `fourierCoeff_fourier`.
* A Fourier monomial `fourier m` is likewise determined by its coefficients.
* The interval form recovers vanishing on `[-π, π]` for the zero function,
  viewed as a continuous `2π`-periodic function on `ℝ`.
-/

namespace MathlibExtTest.Analysis.Fourier.FourierUniquenessTests

open MeasureTheory Filter Topology
open MathlibExt.Analysis.Fourier.AddCircle.FourierUniqueness

variable {T : ℝ} [hT : Fact (0 < T)]

/-- Uniqueness recovers the zero function. -/
example : (0 : C(AddCircle T, ℂ)) = 0 := by
  apply eq_zero_of_fourierCoeff_eq_zero (f := 0)
  intro n
  simp [fourierCoeff]

/-- The constant function `1` has coefficients `Pi.single 0 1`. -/
example (n : ℤ) :
    fourierCoeff (1 : C(AddCircle T, ℂ)) n = (Pi.single (0 : ℤ) (1 : ℂ) : ℤ → ℂ) n := by
  have h1 : (1 : C(AddCircle T, ℂ)) = fourier 0 := by
    ext x
    simp
  rw [h1]
  exact congr_fun (fourierCoeff_fourier 0) n

/-- The constant function `1` is determined by its coefficients. -/
example {f : C(AddCircle T, ℂ)}
    (h : ∀ n : ℤ, fourierCoeff f n = (Pi.single (0 : ℤ) (1 : ℂ) : ℤ → ℂ) n) :
    f = 1 := by
  apply eq_of_fourierCoeff_eq (g := 1)
  intro n
  rw [h n]
  have h1 : (1 : C(AddCircle T, ℂ)) = fourier 0 := by
    ext x
    simp
  rw [h1]
  exact (congr_fun (fourierCoeff_fourier 0) n).symm

/-- A Fourier monomial is determined by its coefficients. -/
example {f : C(AddCircle T, ℂ)} {m : ℤ}
    (h : ∀ n : ℤ, fourierCoeff f n = (Pi.single m (1 : ℂ) : ℤ → ℂ) n) :
    f = fourier m := by
  apply eq_of_fourierCoeff_eq (g := fourier m)
  intro n
  rw [h n]
  exact (congr_fun (fourierCoeff_fourier m) n).symm

/-- Interval form: the zero function on `[-π, π]`, viewed as a continuous
`2π`-periodic function on `ℝ`, has vanishing `fourierCoeffOn` coefficients
and is recovered as zero on the whole interval. -/
example (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    (0 : ℝ → ℂ) x = 0 := by
  have hv := eq_zero_of_fourierCoeffOn_eq_zero (a := -Real.pi) (T := 2 * Real.pi)
      (by positivity) (f := (0 : ℝ → ℂ)) continuous_const (by simp)
      (fun n => by rw [fourierCoeffOn_eq_integral]; simp)
  exact hv x ⟨hx.1, by
    have h2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [h2]
    exact hx.2⟩

end MathlibExtTest.Analysis.Fourier.FourierUniquenessTests
