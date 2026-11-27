/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.CSTRSecondOrder
import Mathlib.Tactic.NormNum

/-! Check the second-order profile at the admissibility threshold and at a large positive deviation. -/

namespace Engineering.Process.CSTR.Tests

open Filter
open scoped Topology

-- With D = k = c* = 1 and inlet concentration 2, λ = 3. The deviation 4 is outside
-- the sufficient absolute-value margin but still gives a global solution converging to zero.
example : Tendsto (fun t : ℝ => 4 * Real.exp (-3 * t) /
    (1 + (4 / (3 : ℝ)) * (1 - Real.exp (-3 * t)))) atTop (𝓝 0) := by
  have h := second_order_linearization 1 1 2 1 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hlimit := (h.2.2.1 (by norm_num)).2.2
  norm_num at hlimit ⊢
  exact hlimit

-- At d = -λ/k the denominator never vanishes at a finite nonnegative time.
example : ¬ ∃ t : ℝ, 0 ≤ t ∧ 1 + (-1 : ℝ) * (1 - Real.exp (-3 * t)) = 0 := by
  have h := second_order_linearization 1 1 2 1 (-3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hnone := not_congr h.2.2.2.2
  norm_num at hnone ⊢

end Engineering.Process.CSTR.Tests
