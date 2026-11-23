/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hermite cubic end-data realization

## i. Overview

The cubic on `[0, L]` with prescribed end values and end slopes is
written in the scaled coordinate `u = x / L` with the standard Hermite
basis. Its end values and slopes are the prescribed data, and it is
the unique cubic with those four end conditions.

## ii. Key results

- `HermiteCubic.hermite_end_values`: end values.
- `HermiteCubic.hermite_end_slopes`: end slopes.
- `HermiteCubic.hermite_unique`: uniqueness among cubics.

## iii. Table of contents

- A. The Hermite cubic

## iv. References

- Standard Hermite interpolation, e.g. R. L. Burden and J. D. Faires,
  *Numerical Analysis*, chapter 3 (Hermite interpolation).

## A. The Hermite cubic
-/

@[expose] public section

namespace HermiteCubic

/-- The cubic on `[0, L]` (as a function of `x`) with end values
`v1, v2` and end slopes `t1, t2`, in the standard Hermite form. -/
noncomputable def hermite (L v1 t1 v2 t2 x : ℝ) : ℝ :=
  (2 * (x / L) ^ 3 - 3 * (x / L) ^ 2 + 1) * v1
    + (x / L) ^ 2 * (3 - 2 * (x / L)) * v2
    + ((x / L) ^ 3 - 2 * (x / L) ^ 2 + x / L) * L * t1
    + ((x / L) ^ 3 - (x / L) ^ 2) * L * t2

/-- Derivative of a cubic polynomial function. -/
theorem deriv_cubic (A B C D y : ℝ) :
    deriv (fun x : ℝ => A * x ^ 3 + B * x ^ 2 + C * x + D) y
      = 3 * A * y ^ 2 + 2 * B * y + C := by
  have hfun : (fun x : ℝ => A * x ^ 3 + B * x ^ 2 + C * x + D)
      = fun x => (Polynomial.C A * Polynomial.X ^ 3 + Polynomial.C B * Polynomial.X ^ 2
        + Polynomial.C C * Polynomial.X + Polynomial.C D).eval x := by
    funext x
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
  rw [hfun, Polynomial.deriv]
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_zero]
  ring

/-- The Hermite cubic takes the prescribed end values. -/
theorem hermite_end_values {L : ℝ} (hL : L ≠ 0) (v1 t1 v2 t2 : ℝ) :
    hermite L v1 t1 v2 t2 0 = v1 ∧ hermite L v1 t1 v2 t2 L = v2 := by
  constructor
  · simp [hermite]
  · have hLL : L / L = 1 := div_self hL
    simp only [hermite, hLL, one_pow]
    ring

/-- The Hermite cubic takes the prescribed end slopes. -/
theorem hermite_end_slopes {L : ℝ} (hL : L ≠ 0) (v1 t1 v2 t2 : ℝ) :
    deriv (hermite L v1 t1 v2 t2) 0 = t1
      ∧ deriv (hermite L v1 t1 v2 t2) L = t2 := by
  have hfun : hermite L v1 t1 v2 t2
      = fun x : ℝ => ((2 * v1 - 2 * v2 + L * t1 + L * t2) / L ^ 3) * x ^ 3
        + (((-3 * v1 + 3 * v2 - 2 * L * t1 - L * t2) / L ^ 2)) * x ^ 2
        + t1 * x + v1 := by
    funext x
    simp only [hermite]
    field_simp
    ring
  rw [hfun]
  simp only [deriv_cubic]
  constructor
  · simp
  · field_simp
    ring

/-- Uniqueness: any cubic polynomial function of degree at most three
matching the four end conditions equals the Hermite cubic everywhere.
Stated for functions given as `fun x => a*x^3+b*x^2+c*x+d`. -/
theorem hermite_unique {L : ℝ} (hL : 0 < L) (v1 t1 v2 t2 a b c d : ℝ)
    (h0 : a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d = v1)
    (hL0 : a * L ^ 3 + b * L ^ 2 + c * L + d = v2)
    (hd0 : 3 * a * 0 ^ 2 + 2 * b * 0 + c = t1)
    (hdL : 3 * a * L ^ 2 + 2 * b * L + c = t2) (x : ℝ) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = hermite L v1 t1 v2 t2 x := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hd : d = v1 := by linear_combination h0
  have hc : c = t1 := by linear_combination hd0
  simp only [hd, hc] at hL0 hdL ⊢
  have ha : a * L ^ 3 = (t1 + t2) * L + 2 * (v1 - v2) := by
    linear_combination L * hdL - 2 * hL0
  have hb : b * L ^ 3
      = -2 * t1 * L ^ 2 - 3 * v1 * L + 3 * v2 * L - t2 * L ^ 2 := by
    linear_combination 3 * L * hL0 - L ^ 2 * hdL
  have hL3 : L ^ 3 ≠ 0 := pow_ne_zero 3 hLne
  have ha' : a = ((t1 + t2) * L + 2 * (v1 - v2)) / L ^ 3 := by
    rw [eq_div_iff hL3]
    exact ha
  have hb' : b
      = (-2 * t1 * L ^ 2 - 3 * v1 * L + 3 * v2 * L - t2 * L ^ 2) / L ^ 3 := by
    rw [eq_div_iff hL3]
    exact hb
  rw [ha', hb']
  simp only [hermite]
  field_simp
  ring

end HermiteCubic
