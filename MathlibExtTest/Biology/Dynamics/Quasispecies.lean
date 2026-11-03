/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.Quasispecies
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Tests for Eigen's error threshold: concrete equilibria, the threshold boundary, the junk
value at `σ = 1`, and solutions witnessing both convergence theorems. -/

open Filter Topology Real

namespace MathlibExtTest.Biology.Dynamics.Quasispecies

open MathlibExt.Biology.Dynamics.Quasispecies

/-- Error-free copying (`Q = 1`): the master takes over, `x* = 1`. -/
example : masterEquilibrium 2 1 = 1 := by norm_num [masterEquilibrium]

/-- `σ = 3`, `Q = 1/2`: `x* = (3/2 - 1)/(3 - 1) = 1/4`. -/
example : masterEquilibrium 3 (1 / 2) = 1 / 4 := by norm_num [masterEquilibrium]

/-- At the threshold `σ Q = 1` the interior equilibrium merges with `0`. -/
example : masterEquilibrium 2 (1 / 2) = 0 := by norm_num [masterEquilibrium]

/-- Below the threshold the interior equilibrium is negative (not a frequency). -/
example : masterEquilibrium 2 (1 / 4) < 0 := by norm_num [masterEquilibrium]

/-- Junk value outside the domain `σ > 1`: `x / 0 = 0`. -/
example (Q : ℝ) : masterEquilibrium 1 Q = 0 := by simp [masterEquilibrium]

example : masterField 3 (1 / 2) (1 / 4) = 0 :=
  (masterField_eq_zero_iff (by norm_num)).2 (Or.inr (by norm_num [masterEquilibrium]))

example : 0 < masterEquilibrium 3 (1 / 2) ↔ 1 < 3 * (1 / 2 : ℝ) :=
  masterEquilibrium_pos_iff (by norm_num) _

/-- With `μ = 0` mutations per copy the master persists iff `σ > 1`, i.e. `0 < log σ`. -/
example : 0 < masterEquilibrium 2 (exp (-0)) := by
  rw [masterEquilibrium_exp_pos_iff (by norm_num)]; exact log_pos (by norm_num)

example : (1 : ℝ) < 2 * (1 / 2) ^ 0 ↔ ((0 : ℕ) : ℝ) < log 2 / (-log (1 / 2)) :=
  one_lt_mul_pow_iff (by norm_num) (by norm_num) (by norm_num) 0

/-- **Non-vacuity witness, above threshold.** The constant solution `x ≡ 1/4` for `σ = 3`,
`Q = 1/2`. -/
example : Tendsto (fun _ : ℝ ↦ (1 / 4 : ℝ)) atTop (𝓝 (masterEquilibrium 3 (1 / 2))) :=
  tendsto_master_of_one_lt (by norm_num) (by norm_num)
    (fun t _ ↦ by
      convert hasDerivAt_const t (1 / 4 : ℝ) using 1
      norm_num [masterField])
    (by norm_num)

/-- **Non-vacuity witness, at threshold.** For `σ = 2`, `Q = 1/2` the master equation is
`x' = -x²`, solved by `x(t) = 1/(1 + t)` on `t ≥ 0`. -/
example : Tendsto (fun t : ℝ ↦ 1 / (1 + t)) atTop (𝓝 0) :=
  tendsto_master_zero_of_le_one (σ := 2) (Q := 1 / 2) (by norm_num) (by norm_num)
    (fun t ht ↦ by
      have h1 : (1 + t) ≠ 0 := by linarith
      have h := ((hasDerivAt_id' t).const_add 1).inv h1
      simp only [one_div]
      convert h using 1
      simp [masterField]; field_simp; ring)
    (by norm_num)

end MathlibExtTest.Biology.Dynamics.Quasispecies
