/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Transfer.Growth

namespace ControlTheory.StateSpaceCoeffs

private noncomputable def accG : StateSpaceCoeffs ℝ ℝ ℝ ℝ :=
  ⟨1, 1, 1, 0⟩

-- Zero-rate edge case: `A = 0`-shaped decay is not needed; for the
-- accumulator with unit input the bound holds with `M = K = 1`,
-- `ρ = r = 1` and `q = 2`: the state at `k = 2` is `2` and the bound
-- is `1 * (0 + 1 / 2) * 3 * 4 = 6`.
example : ‖dtTraj accG (fun _ => (1 : ℝ)) 0 2‖ ≤
    1 * (‖(0 : ℝ)‖ + ‖accG.B‖ * 1 / 2) * (1 + 2) * 2 ^ 2 := by
  have h := dtTraj_growth accG (fun _ => (1 : ℝ)) 0 (M := 1) (K := 1)
    (ρ := 1) (r := 1) (q := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_ ?_ (by norm_num) (by norm_num) 2
  · convert h using 2 <;> norm_num [accG]
  · intro k x
    simp [accG]
  · intro k
    simp

end ControlTheory.StateSpaceCoeffs
