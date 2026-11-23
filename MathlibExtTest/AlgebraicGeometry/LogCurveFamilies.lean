/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.LogCurveFamilies
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section

open Polynomial DualNumber

namespace LogCurveFamiliesTest

/-! A log marking is pinned on the family, not only on geometric fibres. Over the dual numbers
the chart functions `x` and `x - ε` agree after every map to a field, but only `x` vanishes on the
section `x = 0`; `LogCurve.markingEquation` asks for the latter. -/

/-- Every map from the dual numbers to a field kills `ε`. -/
example (K : Type) [Field K] (φ : DualNumber ℚ →+* K) : φ ε = 0 := by
  have h : φ ε * φ ε = 0 := by rw [← map_mul, eps_mul_eps, map_zero]
  exact mul_self_eq_zero.mp h

/-- The shifted chart function does not vanish on the section `x = 0`. -/
example : (X - C (ε : DualNumber ℚ)).eval 0 ≠ 0 := by
  rw [eval_sub, eval_X, eval_C, zero_sub, neg_ne_zero]
  intro h
  have := congrArg TrivSqZeroExt.snd h
  simp at this

/-- The given chart function does. -/
example : (X : (DualNumber ℚ)[X]).eval 0 = 0 := by simp

/-- Why the base component of the marking ghost must be trivial: with base chart `1 ↦ ε`, the
mixed section with ghost `(1, 1)` has function `ε (x - ε)`, which does vanish on `x = 0`
although the shifted marking equation `x - ε` does not. -/
example : (C (ε : DualNumber ℚ) * (X - C ε)).eval 0 = 0 := by
  rw [eval_mul, eval_C, eval_sub, eval_X, eval_C, zero_sub, mul_neg, eps_mul_eps, neg_zero]

end LogCurveFamiliesTest
