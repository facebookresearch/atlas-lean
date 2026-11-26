/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.EhrlingInequality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for Ehrling's inequality -/

open MathlibExt.Analysis.FunctionalAnalysis.EhrlingInequalityWanted

-- For the identity followed by multiplication by a positive scalar a, evaluating the
-- uniform estimate at 1 forces the Ehrling constant for ε = 1/2 to satisfy C * a ≥ 1/2.
example (a : ℝ) (ha : 0 < a) :
    ∃ C > 0, 1 / 2 ≤ C * a ∧ ∀ u : ℝ, |u| ≤ |u| / 2 + C * |a * u| := by
  let I := ContinuousLinearMap.id ℝ ℝ
  obtain ⟨C, hC, h⟩ := ehrling_inequality I (a • I) isCompactOperator_id
    Function.injective_id (mul_right_injective₀ ha.ne') (1 / 2) (by norm_num)
  have hbound (u : ℝ) : |u| ≤ |u| / 2 + C * |a * u| := by
    simpa [I, Real.norm_eq_abs, div_eq_inv_mul] using h u
  refine ⟨C, hC, ?_, hbound⟩
  have hone := hbound 1
  rw [abs_one, mul_one, abs_of_pos ha] at hone
  linarith
