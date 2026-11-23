/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Physiology.RespiratoryMechanics

/-! Tests: numeric agreement and free expiration. -/

namespace PhyslibExtTest.Physiology.RespiratoryMechanics

open PhyslibExt.Physiology.RespiratoryMechanics

/-- Numeric instance of the agreement, exercised through the API. -/
example : (2:ℝ) * deriv (fun u => (1 / (1:ℝ)) * 3 + (4 - (1 / (1:ℝ)) * 3) *
    Real.exp (-u / (2 * (1 / (1:ℝ))))) 1 +
    1 * ((1 / (1:ℝ)) * 3 + (4 - (1 / (1:ℝ)) * 3) *
    Real.exp (-(1:ℝ) / (2 * (1 / (1:ℝ))))) = 3 :=
  respiratory_response (by norm_num) (by norm_num)

/-- Free expiration solves the zero-drive equation at `R = 2`,
`E = 1`, `V0 = 4`, `t = 3`. -/
example : (2:ℝ) * deriv (fun u => 4 * Real.exp (-u / (2 * (1 / (1:ℝ))))) 3 +
    1 * (4 * Real.exp (-(3:ℝ) / (2 * (1 / (1:ℝ))))) = 0 :=
  respiratory_expiration (by norm_num) (by norm_num)

end PhyslibExtTest.Physiology.RespiratoryMechanics
