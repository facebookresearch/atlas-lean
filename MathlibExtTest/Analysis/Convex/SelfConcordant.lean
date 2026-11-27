/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.SelfConcordant

open MathlibExt.Analysis.Convex.SelfConcordant

-- `-log` is self-concordant on the positive ray.
example : IsSelfConcordant (fun x : ℝ => -Real.log x) (Set.Ioi 0) :=
  isSelfConcordantBarrier_neg_log.2.1

-- Its Newton decrement is at most `1` everywhere: at `x = 2` in direction `h = 3`,
-- `|DF(x)[h]| = 3/2 ≤ √1 · (D²F(x)[h, h])^{1/2}`.
example : |deriv (fun t : ℝ => -Real.log (2 + t • (3 : ℝ))) 0| ≤
    √1 * √(iteratedDeriv 2 (fun t : ℝ => -Real.log (2 + t • (3 : ℝ))) 0) :=
  isSelfConcordantBarrier_neg_log.2.2 2 (by norm_num) 3

-- The barrier property is not automatic: the constant `0` is smooth and convex on `(0, ∞)` but
-- does not blow up at the boundary point `0`, so it is not self-concordant there.
example : ¬ IsSelfConcordant (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 0) := by
  rintro ⟨-, -, -, -, -, hbar, -⟩
  have := hbar 0 (by simp)
  exact Filter.not_tendsto_const_atTop 0 _ this
