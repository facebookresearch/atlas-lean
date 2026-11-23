/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.RobustLinearProgramming

open scoped RealInnerProductSpace

namespace MathlibExt.Analysis.Convex.RobustLinearProgramming

-- The minimum of `⟪u, v⟫` over the unit ball: on `ℝ`, `1 + u * 1 ≥ 0` for `|u| ≤ 1`.
example : ∀ u : ℝ, ‖u‖ ≤ 1 → 0 ≤ 1 + ⟪u, (1 : ℝ)⟫ :=
  (forall_norm_le_one_le_add_inner_iff 1 (1 : ℝ)).mpr (by simp)

-- ... but `1/2 + u * 1 ≥ 0` fails for some `|u| ≤ 1`.
example : ¬ ∀ u : ℝ, ‖u‖ ≤ 1 → 0 ≤ 1 / 2 + ⟪u, (1 : ℝ)⟫ := by
  rw [forall_norm_le_one_le_add_inner_iff]; norm_num

-- On `E = U = ℝ`, the uncertain constraint `a x - b ≥ 0` with `a = 2 + u`, `b = 1`, `|u| ≤ 1`, is
-- robustly satisfied exactly when `|x| ≤ 2 x - 1`, i.e. `x ≥ 1`.
example (x : ℝ) :
    (∀ u : ℝ, ‖u‖ ≤ 1 → 0 ≤ ⟪(2 : ℝ) + ContinuousLinearMap.id ℝ ℝ u, x⟫ - (1 + ⟪(0 : ℝ), u⟫)) ↔
      |x| ≤ 2 * x - 1 := by
  rw [robust_linear_constraint_iff, ContinuousLinearMap.adjoint_id]
  simp [Real.norm_eq_abs, mul_comm]

-- The robust objective: `(1 + u) x ≤ t` for all `|u| ≤ 1` iff `x + |x| ≤ t`.
example (x t : ℝ) :
    (∀ u : ℝ, ‖u‖ ≤ 1 → ⟪(1 : ℝ) + ContinuousLinearMap.id ℝ ℝ u, x⟫ ≤ t) ↔ x + |x| ≤ t := by
  rw [robust_objective_le_iff, ContinuousLinearMap.adjoint_id]
  simp [Real.norm_eq_abs]

end MathlibExt.Analysis.Convex.RobustLinearProgramming
