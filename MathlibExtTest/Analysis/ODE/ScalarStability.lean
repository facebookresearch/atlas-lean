/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.ScalarStability
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

@[expose] public section

namespace MathlibExtTest.Analysis.ODE.ScalarStability

open MathlibExt.Analysis.ODE.ScalarStability

/-- Test 1: `f x = -x` at equilibrium `0`. -/
example :
    ∃ δ C α : ℝ, 0 < δ ∧ 0 < C ∧ 0 < α ∧ ∀ x : ℝ → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x ((fun x => -x) (x t)) t) → |x 0 - 0| < δ →
        ∀ t, 0 ≤ t → |x t - 0| ≤ C * Real.exp (-(α * t)) * |x 0 - 0| :=
  scalar_sign_decay_of_hasDerivAt (f := fun x => -x) (xstar := 0) (f' := -1)
    (by simp) (HasDerivAt.neg (hasDerivAt_id (0 : ℝ))) (by norm_num)

/-- Test 2: `f x = -2 * (x - 1)` at nonzero equilibrium `1`.
Note: the shifted field has the same derivative `-2` at the equilibrium; the
unshifted `-2 * x` does not vanish at `1`, so it is not an equilibrium there. -/
example :
    ∃ δ C α : ℝ, 0 < δ ∧ 0 < C ∧ 0 < α ∧ ∀ x : ℝ → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x ((fun x => -2 * (x - 1)) (x t)) t) → |x 0 - 1| < δ →
        ∀ t, 0 ≤ t → |x t - 1| ≤ C * Real.exp (-(α * t)) * |x 0 - 1| :=
  scalar_sign_decay_of_hasDerivAt (f := fun x => -2 * (x - 1)) (xstar := 1) (f' := -2)
    (by norm_num)
    (by
      have h := HasDerivAt.const_mul (-2)
        (HasDerivAt.sub_const (1 : ℝ) (hasDerivAt_id (1 : ℝ)))
      simpa using h)
    (by norm_num)

end MathlibExtTest.Analysis.ODE.ScalarStability
