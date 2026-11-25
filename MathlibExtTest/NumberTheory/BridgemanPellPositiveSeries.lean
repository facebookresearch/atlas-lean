/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.IsSquare
import MathlibExt.NumberTheory.BridgemanPellPositiveSeries

/-! # The positive Pell solution `3 + 2 * √2` -/

open Real

namespace MathlibExtTest.BridgemanPellPositiveSeries

private def coeffs : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | k + 1 =>
    let (x, y) := coeffs k
    (3 * x + 4 * y, 2 * x + 3 * y)

example :
    let L (x : ℝ) := (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    L (1 / (3 + 2 * √2) ^ 2) = (∑' k : ℕ, L (4 / ((coeffs (k + 2)).2 : ℝ) ^ 2)) ∧
      ∀ k, ∃ m : ℤ, (coeffs k).2 = 2 * (m : ℚ) := by
  intro L
  have h := MetaMathlibExt.rogersDilog_pell_positive_series
    (n := 2) (a := 3) (b := 2) (A := fun k => (coeffs k).1) (B := fun k => (coeffs k).2)
    (hn := by norm_num) (by norm_num) (by norm_num) (by norm_num) rfl rfl
    (by intro k; norm_num [coeffs]) (by intro k; simp [coeffs])
  refine ⟨?_, h.2 ⟨3, 2, by norm_num, by norm_num⟩⟩
  simpa [L, show (2 : ℝ) ^ 2 = 4 by norm_num] using h.1

end MathlibExtTest.BridgemanPellPositiveSeries
