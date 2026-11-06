/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Catalan's constant
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace Real

/-- **Catalan's constant.** Catalan's constant is the real number
$G = \sum_{n=0}^{\infty} \frac{(-1)^n}{(2n+1)^2}$. -/
noncomputable def catalanConstant : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2

/-- **The series for Catalan's constant converges absolutely.** The series
$\sum_{n=0}^{\infty} \frac{(-1)^n}{(2n+1)^2}$ converges absolutely: its terms are bounded in
absolute value by $\frac{1}{(n+1)^2}$, and $\sum_{n=0}^{\infty} \frac{1}{(n+1)^2}$ converges. -/
theorem summable_catalanConstant_terms :
    Summable (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) ?_ ?_
  · have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 := (summable_nat_add_iff 1).mpr h
    refine h2.congr (fun n => ?_)
    push_cast
    ring
  · intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_div]
    simp only [abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 * (n : ℝ) + 1 by positivity),
      abs_neg, abs_one, one_pow]
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **Catalan's constant as a series.** Catalan's constant $G$ equals
$\sum_{n=0}^{\infty} \frac{(-1)^n}{(2n+1)^2}$. -/
theorem catalanConstant_eq_tsum :
    catalanConstant = ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 :=
  rfl

/-- **The series for Catalan's constant converges to it.** The series
$\sum_{n=0}^{\infty} \frac{(-1)^n}{(2n+1)^2}$ converges unconditionally, and its sum is Catalan's
constant $G$. -/
theorem hasSum_catalanConstant :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2)
      catalanConstant :=
  summable_catalanConstant_terms.hasSum

end Real
