/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Biomechanics.MusclePower

/-! Tests for the muscle power maximum: the roadmap's numerical case
`a = 1`, `F0 = 3`, `b = 2` giving `Fstar = 1`, and endpoint powers. -/

namespace PhyslibExtTest.Biomechanics.MusclePower

open PhyslibExt.Biomechanics.MusclePower

/-- At `a = 1`, `F0 = 3`: `Fstar = sqrt 4 - 1 = 1`, strictly interior,
with maximal power `1 * (2 * 2 / 2) = 2`. -/
example : let Fstar := Real.sqrt (1 * (1 + 3)) - 1
    Fstar = 1 ∧ ∀ F : ℝ, 0 ≤ F → F ≤ 3 →
      F * (2 * (3 - F) / (F + 1)) ≤ Fstar * (2 * (3 - Fstar) / (Fstar + 1)) := by
  have h := muscle_power_max (a := 1) (b := 2) (F0 := 3) one_pos (by norm_num) (by norm_num)
  refine ⟨?_, h.2.2.2⟩
  have h2 : Real.sqrt ((1 : ℝ) * (1 + 3)) = 2 := by
    rw [show (1 * (1 + 3) : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  show Real.sqrt ((1 : ℝ) * (1 + 3)) - 1 = 1
  rw [h2]; norm_num

/-- Endpoint powers vanish: at `F = 0` and at `F = F0`. -/
example : (0 : ℝ) * (2 * (3 - 0) / (0 + 1)) = 0 ∧
    (3 : ℝ) * (2 * (3 - 3) / (3 + 1)) = 0 := by norm_num

/-- Power at `F = 1` under `a = 1`, `F0 = 3`, `b = 2` is `2`. -/
example : hillPower 1 2 3 1 = 2 := by
  have h := muscle_power_formula (a := 1) (b := 2) (F0 := 3) (F := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

/-- Constant force `c = 1` with `x' = 2`: work over `[0, 3]` is
`1 * (x 3 - x 0)`. -/
example {x : ℝ → ℝ} (hx : ∀ t ∈ Set.uIcc 0 3, HasDerivAt x (2 * (3 - 1) / (1 + 1)) t) :
    (∫ _t in (0:ℝ)..3, (1:ℝ) * (2 * (3 - 1) / (1 + 1))) = 1 * (x 3 - x 0) :=
  muscle_work_constant (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hx

end PhyslibExtTest.Biomechanics.MusclePower
