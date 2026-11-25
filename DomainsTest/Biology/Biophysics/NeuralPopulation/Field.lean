/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.NeuralPopulation.Field
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Tests for the Wilson-Cowan field derivatives with an explicit
linear gain `fE z = 2 * z` (derivative `2`), including the refractory
term, and the `r = 0` simplification. -/

namespace MathlibExtTest.Biology.Biophysics.NeuralPopulation.Field

open MathlibExt.Biology.Biophysics.NeuralPopulation.Field

/-- With `fE z = 2z`, `tauE = 1`, `rE = 1/2`, weights `wEI = 3`,
`wEE = 4`, at `x = y = 0`, `hE = 0`: `∂E/∂x` has derivative
`-1 - (1/2)(0) + (1)(2)(4) = 7`. -/
example : HasDerivAt
    (fun x' : ℝ => (-x' + (1 - (1/2) * x') * (2 * (0 - 3 * 0 + 4 * x'))) / 1)
    ((-1 - (1/2) * (2 * (0 - 3 * 0 + 4 * 0)) + (1 - (1/2) * 0) * 2 * 4) / 1) 0 := by
  have h := (rate_field_E_deriv (tauE := 1) (rE := 1/2) (x := 0) (y := 0)
    (hE := 0) (wEI := 3) (wEE := 4) (fE := fun z => 2 * z) (fE' := 2)
    (by
      have hid : HasDerivAt (fun z : ℝ => z) 1 (0:ℝ) := hasDerivAt_id 0
      simpa using hid.const_mul (2 : ℝ))).1
  exact h

/-- At `rE = 0` the refractory term vanishes from `∂E/∂x`. -/
example : HasDerivAt
    (fun x' : ℝ => (-x' + (1 - 0 * x') * (2 * (0 - 3 * 0 + 4 * x'))) / 1)
    ((-1 - 0 * (2 * (0 - 3 * 0 + 4 * 0)) + (1 - 0 * 0) * 2 * 4) / 1) 0 := by
  have h := (rate_field_E_deriv (tauE := 1) (rE := 0) (x := 0) (y := 0)
    (hE := 0) (wEI := 3) (wEE := 4) (fE := fun z => 2 * z) (fE' := 2)
    (by
      have hid : HasDerivAt (fun z : ℝ => z) 1 (0:ℝ) := hasDerivAt_id 0
      simpa using hid.const_mul (2 : ℝ))).1
  exact h

/-- Refractory-sensitive witness: `hE = 1`, `fE z = 2z` at `x = y = 0`.
With `rE = 1/2` the derivative is `6`; the omitted-`-rE * fE` value
would be `7`. -/
example : HasDerivAt
    (fun x' : ℝ => (-x' + (1 - (1/2) * x') * (2 * (1 - 3 * 0 + 4 * x'))) / 1) 6 0 := by
  have h := (rate_field_E_deriv (tauE := 1) (rE := 1/2) (x := 0) (y := 0)
    (hE := 1) (wEI := 3) (wEE := 4) (fE := fun z => 2 * z) (fE' := 2)
    (by
      have hid : HasDerivAt (fun z : ℝ => z) 1 (1:ℝ) := hasDerivAt_id 1
      simpa using hid.const_mul (2 : ℝ))).1
  have h6 : ((-1 - (1/2) * (2 * (1 - 3 * 0 + 4 * 0)) + (1 - (1/2) * 0) * 2 * 4) / 1 : ℝ) = 6 := by
    norm_num
  rw [h6] at h
  exact h

/-- E cross-partial `∂E/∂y` at the same witness:
`(1)(2)(-3) = -6`. -/
example : HasDerivAt
    (fun y' : ℝ => (-(0:ℝ) + (1 - (1/2) * 0) * (2 * (1 - 3 * y' + 4 * 0))) / 1) (-6) 0 := by
  have h := (rate_field_E_deriv (tauE := 1) (rE := 1/2) (x := 0) (y := 0)
    (hE := 1) (wEI := 3) (wEE := 4) (fE := fun z => 2 * z) (fE' := 2)
    (by
      have hid : HasDerivAt (fun z : ℝ => z) 1 (1:ℝ) := hasDerivAt_id 1
      simpa using hid.const_mul (2 : ℝ))).2
  have h6 : ((1 - (1/2) * 0) * 2 * (-3) / 1 : ℝ) = -6 := by norm_num
  rw [h6] at h
  exact h

/-- I partials with `fI z = 3z`, `hI = 1`, `rI = 1/3`, weights
`wIE = 2`, `wII = 5`, at `x = y = 0`: `∂I/∂y = -1 - (1/3)(3) + (1)(3)(-5) = -17`,
`∂I/∂x = (1)(3)(2) = 6`. -/
example : HasDerivAt
    (fun y' : ℝ => (-y' + (1 - (1/3) * y') * (3 * (1 + 2 * 0 - 5 * y'))) / 1) (-17) 0 ∧
    HasDerivAt
    (fun x' : ℝ => (-(0:ℝ) + (1 - (1/3) * 0) * (3 * (1 + 2 * x' - 5 * 0))) / 1) 6 0 := by
  have h := rate_field_I_deriv (tauI := 1) (rI := 1/3) (x := 0) (y := 0)
    (hI := 1) (wIE := 2) (wII := 5) (fI := fun z => 3 * z) (fI' := 3)
    (by
      have hid : HasDerivAt (fun z : ℝ => z) 1 (1:ℝ) := hasDerivAt_id 1
      simpa using hid.const_mul (3 : ℝ))
  have h1 : ((-1 - (1/3) * (3 * (1 + 2 * 0 - 5 * 0)) + (1 - (1/3) * 0) * 3 * (-5)) / 1 : ℝ) = -17 := by
    norm_num
  have h2 : ((1 - (1/3) * 0) * 3 * 2 / 1 : ℝ) = 6 := by norm_num
  rw [h1] at h
  rw [h2] at h
  exact h

end MathlibExtTest.Biology.Biophysics.NeuralPopulation.Field
