/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Physiology.Windkessel

/-! Tests: constant-flow transient agreement. -/

namespace PhyslibExtTest.Physiology.Windkessel

open PhyslibExt.Physiology.Windkessel

/-- Numeric transient agreement at `R = 2`, `C = 3`. -/
example : (3:ℝ) * deriv (fun u => 2 * 5 + (7 - 2 * 5) *
    Real.exp (-u / (2 * 3))) 1 =
    5 - (2 * 5 + (7 - 2 * 5) * Real.exp (-(1:ℝ) / (2 * 3))) / 2 :=
  windkessel_transient (by norm_num) (by norm_num)

end PhyslibExtTest.Physiology.Windkessel
