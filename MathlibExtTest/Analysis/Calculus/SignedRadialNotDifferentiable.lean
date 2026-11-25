/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.SignedRadialNotDifferentiable

/-!
# Test for the signed radial function

Instantiate all three branch hypotheses with the piecewise function from the statement.
-/

namespace MathlibExt.Analysis.Calculus.SignedRadialNotDifferentiableWanted

example : ¬ DifferentiableAt ℝ (fun p : ℝ × ℝ ↦
    if 0 < p.2 then Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
    else if p.2 < 0 then -Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
    else p.1) (0, 0) := by
  apply not_differentiableAt_signed_norm_zero
  · intro x y hy
    simp [hy]
  · intro x
    simp
  · intro x y hy
    simp [hy, hy.not_gt]

end MathlibExt.Analysis.Calculus.SignedRadialNotDifferentiableWanted
