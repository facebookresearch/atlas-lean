/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Algebra.ExponentialLimit

/-!
# Tests for the compound-interest limit in a Banach algebra

The scalar case `(1 + x / M) ^ M → exp x` recovered in `ℝ`, the case `m M = 0` (limit `1`),
the general-time-scale limit with `ε N = ((N + 1) ^ 2)⁻¹` and `(N + 1) ^ 2` steps, and the
telescoping estimate at `m = 0` and `m = 1`.
-/

@[expose] public section

open Filter Topology NormedSpace

namespace MathlibExtTest.Analysis.Normed.Algebra.ExponentialLimit

/-- The scalar compound-interest limit, recovered in `ℝ`. -/
example (x : ℝ) :
    Tendsto (fun M : ℕ => (1 + (M : ℝ)⁻¹ • x) ^ M) atTop (𝓝 (exp ((1 : ℝ) • x))) := by
  refine tendsto_one_add_inv_smul_pow tendsto_const_nhds ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with M hM
  rw [div_self (by exact_mod_cast hM)]

/-- Zero steps: the limit is `exp 0 = 1` whatever the increments. -/
example (Y : ℕ → ℝ) (X : ℝ) (hY : Tendsto Y atTop (𝓝 X)) :
    Tendsto (fun M : ℕ => (1 + (M : ℝ)⁻¹ • Y M) ^ (0 : ℕ)) atTop (𝓝 (exp ((0 : ℝ) • X))) :=
  tendsto_one_add_inv_smul_pow hY (by simp)

/-- A general time scale: `ε N = ((N + 1) ^ 2)⁻¹` with `(N + 1) ^ 2` steps, so `m N * ε N = 1`,
recovers `exp x` in `ℝ`. -/
example (x : ℝ) :
    Tendsto (fun N : ℕ => (1 + (((N : ℝ) + 1) ^ 2)⁻¹ • x) ^ ((N + 1) ^ 2)) atTop
      (𝓝 (exp ((1 : ℝ) • x))) := by
  have hsq : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hε : Tendsto (fun N : ℕ => (((N : ℝ) + 1) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsq
  refine tendsto_one_add_smul_pow hε (Eventually.of_forall fun N => inv_pos.2 (by positivity))
    tendsto_const_nhds (tendsto_const_nhds.congr fun N => ?_)
  push_cast
  rw [mul_inv_cancel₀ (by positivity)]

/-- The telescoping estimate at `m = 1` is `‖a - b‖ ≤ ‖a - b‖`. -/
example (a b : ℝ) : ‖a ^ 1 - b ^ 1‖ ≤ (1 : ℕ) * ‖a - b‖ * max ‖a‖ ‖b‖ ^ (1 - 1) :=
  norm_pow_sub_pow_le a b 1

/-- The telescoping estimate at `m = 2` in `ℝ`: `|a² - b²| ≤ 2 |a - b| max(|a|, |b|)`. -/
example : ‖(3 : ℝ) ^ 2 - 1 ^ 2‖ ≤ (2 : ℕ) * ‖(3 : ℝ) - 1‖ * max ‖(3 : ℝ)‖ ‖(1 : ℝ)‖ ^ (2 - 1) :=
  norm_pow_sub_pow_le 3 1 2

end MathlibExtTest.Analysis.Normed.Algebra.ExponentialLimit
