/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.FareyStaircase
import MathlibExt.NumberTheory.FareyStaircaseFareyStaircaseLeFloorDiv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounds on the increment of the Farey staircase

The theorem `fareyStaircase_sub_mem_Icc` bounds the increment `D_n(x) = A_n(x) - A_{n-1}(x)`
of the Farey staircase: it is nonnegative and at most `(log n) / (n * (n - 1))` for `n ≥ 2`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (b) (`integers-2024-A37-lem-8`) (primary text: arXiv:2303.02935).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Bounds on the increment of the Farey staircase.** Let $n \ge 2$ be a natural number and $x$
a real number, and write $A_m$ for the Farey staircase of order $m$. Then
$0 \le A_n(x) - A_{n-1}(x) \le \frac{\log n}{n(n-1)}$, where $\log$ is the natural logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (b) (`integers-2024-A37-lem-8`). -/
public theorem fareyStaircase_sub_mem_Icc {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ fareyStaircase n x - fareyStaircase (n - 1) x ∧
      fareyStaircase n x - fareyStaircase (n - 1) x ≤ Real.log n / (n * (n - 1)) := by
  obtain ⟨hlower, hupper⟩ := fareyStaircase_le_floor_div (by omega : 1 ≤ n) x
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [(fareyStaircase_sub_eq hn x).2]
  refine ⟨mul_nonneg (inv_nonneg.mpr hn1.le) (by linarith), ?_⟩
  calc ((n : ℝ) - 1)⁻¹ * (⌊(n : ℝ) * x⌋ / n - fareyStaircase n x)
      ≤ ((n : ℝ) - 1)⁻¹ * (Real.log n / n) := by gcongr; linarith
    _ = Real.log n / (n * (n - 1)) := by rw [div_mul_eq_div_div_swap]; ring

end

end MetaMathlibExt
