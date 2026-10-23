/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecificLimits.RootTest
import Mathlib.Tactic

namespace MetaMathlibExt

open scoped Topology

/-- The geometric series with ratio `1 / 2` converges, by the root test:
the `n`-th roots are eventually constantly `1 / 2`. -/
example : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
  apply summable_of_root_test_tendsto_lt_one (l := 1 / 2) (by norm_num)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  apply Filter.EventuallyEq.symm
  filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
  have hn_ne : (n : ℕ) ≠ 0 := by omega
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n),
    show (1 : ℝ) / (n : ℝ) = (n : ℝ)⁻¹ from one_div _,
    Real.pow_rpow_inv_natCast (by norm_num) hn_ne]

/-- The geometric series with ratio `2` diverges, by the root test:
the `n`-th roots are eventually constantly `2`. -/
example : ¬Summable (fun n : ℕ => (2 : ℝ) ^ n) := by
  apply not_summable_of_root_test_tendsto_gt_one (l := 2) (by norm_num)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  apply Filter.EventuallyEq.symm
  filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
  have hn_ne : (n : ℕ) ≠ 0 := by omega
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n),
    show (1 : ℝ) / (n : ℝ) = (n : ℝ)⁻¹ from one_div _,
    Real.pow_rpow_inv_natCast (by norm_num) hn_ne]

/-- The v1 `ℝ`-valued form of the root test, with `|x n|` in place of `‖x n‖`,
is the normed-group version above: for real sequences the norm is the
absolute value. -/
example {x : ℕ → ℝ} {l : ℝ} (hl : l < 1)
    (h : Filter.Tendsto (fun n => |x n| ^ ((1 : ℝ) / n)) Filter.atTop (𝓝 l)) :
    Summable x := by
  apply summable_of_root_test_tendsto_lt_one hl
  simpa only [Real.norm_eq_abs] using h

end MetaMathlibExt
