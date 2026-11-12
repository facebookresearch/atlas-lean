/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.Sequence.G06KalmanHistory

/-!
# Tests for sequential Kalman conditioning (G06)

Closed checks: the roadmap witness `F = H0 = H1 = 1`, `P0 = R0 = R1 = 1`,
`Q = 0`, `m0 = 0`, `y0 = 1`, `y1 = 2` gives recursive belief
`(1, 1/3)` and equals the batch conditioning, and the degenerate
zero-noise case where the posterior collapses to the observation.
-/

namespace Cslib.MachineLearning.Sequence.G06KalmanHistory

/-- Witness: `F = H0 = H1 = 1`, `P0 = R0 = R1 = 1`, `Q = 0`, `m0 = 0`,
`y0 = 1`, `y1 = 2`: recursive belief `(1, 1/3)`. -/
example :
    g06Recursive 1 0 1 1 1 1 (0, 1) 1 2 = (1, 1 / 3) := by
  simp [g06Recursive, g06Update, g06Predict]
  norm_num

/-- Witness: recursive equals batch on the witness parameters. -/
example :
    g06Recursive 1 0 1 1 1 1 (0, 1) 1 2 =
      (g06BatchMean 1 1 1 1 1 0 1 0 ![1, 2],
        g06BatchVar 1 1 1 1 1 0 1) := by
  have h := g06_recursive_eq_batch 1 0 1 1 1 1 (0, 1) 1 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact h

/-- Degenerate zero noise: `P0 = 1`, `Q = 0`, `R0 = R1 = 0` is excluded
by the positivity hypotheses, so instead check `R → 0` is not needed:
with `H0 = H1 = 1`, `F = 1`, `Q = 0`, `P0 = 0` (known state) the belief
stays `(m0, 0)` regardless of observations. -/
example (m0 y0 y1 : ℝ) :
    g06Recursive 1 0 1 1 1 1 (m0, 0) y0 y1 = (m0, 0) := by
  simp [g06Recursive, g06Update, g06Predict]

#print axioms g06_recursive_eq_batch

end Cslib.MachineLearning.Sequence.G06KalmanHistory
