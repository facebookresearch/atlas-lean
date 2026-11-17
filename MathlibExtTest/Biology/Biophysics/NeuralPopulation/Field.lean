/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.NeuralPopulation.Field
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

end MathlibExtTest.Biology.Biophysics.NeuralPopulation.Field
