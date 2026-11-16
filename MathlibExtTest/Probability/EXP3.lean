/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.EXP3

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Probability.EXP3

/-- Uniform sampling of two arms with losses `(1, 0)`: the expected estimate
for arm `0` is its loss `1`. -/
example : ∑ j : Fin 2, (1 / 2 : ℝ) * lossEst (fun _ => 1 / 2) ![1, 0] j 0 = 1 :=
  lossEst_expectation (fun _ => 1 / 2) ![1, 0] 0 (by norm_num)

/-- An unsampled arm gets estimate `0`. -/
example : lossEst (fun _ => (1 / 2 : ℝ)) ![1, 0] 1 0 = 0 := by
  simp [lossEst]

/-- The sampled arm gets the importance-weighted loss `l i / p i`. -/
example : lossEst (fun _ => (1 / 2 : ℝ)) ![1, 0] 0 0 = 2 := by
  norm_num [lossEst]

end
