/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.ExpSubExpUniqueFixedPoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open MathlibExt.Analysis.SpecialFunctions.ExpSubExpUniqueFixedPointWanted

-- The global fixed point restricts to the open interval (1, 2).
example : ∃! x : Set.Ioo (1 : ℝ) 2,
    Function.IsFixedPt (fun y : ℝ ↦ Real.exp (y - 1) - Real.exp (1 - y)) (x : ℝ) := by
  obtain ⟨x, hx, huniq⟩ := existsUnique_exp_sub_one_sub_exp_one_sub_eq_self
  have hsinh : 2 * Real.sinh (x - 1) = x := by
    rw [Real.sinh_eq, neg_sub]
    linarith
  have hlo : 1 < x := by
    by_contra! h
    linarith [Real.sinh_le_self_iff.mpr (sub_nonpos.mpr h)]
  have hhi : x < 2 := by
    linarith [Real.self_lt_sinh_iff.mpr (sub_pos.mpr hlo)]
  exact ⟨⟨x, hlo, hhi⟩, hx, fun y hy ↦ Subtype.ext (huniq y hy)⟩
