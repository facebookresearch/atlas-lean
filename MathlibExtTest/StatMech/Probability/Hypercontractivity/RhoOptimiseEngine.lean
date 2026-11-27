/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.RhoOptimiseEngine

/-!
# Tests for `MathlibExt.Probability.Hypercontractivity.RhoOptimiseEngine`

* `∫₀¹ (1 - u)² du = 1/3`.
* `roe_logGain` on one coordinate with degree `1`, coefficient `1` and `δ = 1`, where the master
  bound `Hmaster` holds with equality (`1 ≤ 1^(u/(2-u)) · 1`).
* `roe_V` and `roe_W` at that input.
-/

@[expose] public section

open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.Hypercontractivity.RhoOptimiseEngine

example : ∫ u in (0 : ℝ)..1, (1 - u) ^ 2 = 1 / 3 := by
  rw [roe_integral_one_sub_pow]; norm_num

example : roe_W (fun _ : Fin 1 => 1) (fun _ => 1) = 1 := by simp [roe_W]

example : roe_V (fun _ : Fin 1 => 1) (fun _ => 1) = 1 := by simp [roe_V]

example : roe_V (fun _ : Fin 1 => 1) (fun _ => 1) * Real.log (1 / 1)
    ≤ 2 * roe_W (fun _ : Fin 1 => 1) (fun _ => 1) :=
  roe_logGain (fun _ => zero_le_one) zero_le_one
    (fun u _ _ => by simp [roe_lhs, roe_W])

end MathlibExtTest.StatMech.Probability.Hypercontractivity.RhoOptimiseEngine
