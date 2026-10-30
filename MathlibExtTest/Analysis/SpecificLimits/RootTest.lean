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
    Summable (fun n => |x n|) := by
  have hnorm := summable_norm_of_root_test_tendsto_lt_one (f := x) hl
    (by simpa only [Real.norm_eq_abs] using h)
  simpa only [Real.norm_eq_abs] using hnorm


/-- The negative geometric sequence has root limit `1 / 2`. -/
private theorem negative_half_root_limit :
    Filter.Tendsto (fun n : ℕ => ‖(-1 / 2 : ℝ) ^ n‖ ^ ((1 : ℝ) / n))
      Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  apply Filter.EventuallyEq.symm
  filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
  have hn_ne : (n : ℕ) ≠ 0 := by omega
  rw [norm_pow, show ‖(-1 / 2 : ℝ)‖ = (1 / 2 : ℝ) by norm_num,
    show (1 : ℝ) / (n : ℝ) = (n : ℝ)⁻¹ from one_div _,
    Real.pow_rpow_inv_natCast (by norm_num) hn_ne]

/-- Alternating signs still give absolute convergence below the root threshold. -/
example : Summable (fun n : ℕ => |(-1 / 2 : ℝ) ^ n|) := by
  have hnorm := summable_norm_of_root_test_tendsto_lt_one
    (by norm_num : (1 / 2 : ℝ) < 1) negative_half_root_limit
  simpa only [Real.norm_eq_abs] using hnorm

/-- A large initial term does not affect the root limit or absolute convergence. -/
example : Summable (fun n : ℕ =>
    |if n = 0 then (-1000 : ℝ) else (-1 / 2 : ℝ) ^ n|) := by
  have hroot : Filter.Tendsto
      (fun n : ℕ => ‖if n = 0 then (-1000 : ℝ) else (-1 / 2 : ℝ) ^ n‖ ^ ((1 : ℝ) / n))
      Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
    apply Filter.Tendsto.congr' _ negative_half_root_limit
    filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
    simp [show n ≠ 0 by omega]
  have hnorm := summable_norm_of_root_test_tendsto_lt_one
    (by norm_num : (1 / 2 : ℝ) < 1) hroot
  simpa only [Real.norm_eq_abs] using hnorm

/-- The zero root limit gives the zero-series boundary case. -/
example : Summable (fun _n : ℕ => ‖(0 : ℝ)‖) := by
  apply summable_norm_of_root_test_tendsto_lt_one (l := 0) (by norm_num)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  apply Filter.EventuallyEq.symm
  filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
  rw [norm_zero, Real.zero_rpow (by positivity : (1 : ℝ) / (n : ℝ) ≠ 0)]

/-- At root limit `1`, the constant-one series falls outside the strict criterion. -/
example : Filter.Tendsto (fun n : ℕ => ‖(1 : ℝ)‖ ^ ((1 : ℝ) / n))
    Filter.atTop (𝓝 (1 : ℝ)) := by
  simp

/-- Root limit `1` cannot be included in the convergence implication. -/
example : ¬Summable (fun _n : ℕ => (1 : ℝ)) := by
  rw [summable_const_iff]
  norm_num

end MetaMathlibExt
