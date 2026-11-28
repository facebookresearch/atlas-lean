/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.VerticalLine

import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Tests for Dirichlet series on vertical lines
-/

@[expose] public section

open Complex

namespace VerticalLineTest

example (t : ℝ) : LSeriesSummable 1 ((2 : ℝ) + t * I) :=
  (LSeriesSummable_one_iff.mpr (by norm_num : (1 : ℝ) < (2 : ℂ).re)).vertical t

/-- `|ζ(2 + it)|` is bounded by `∑ n⁻²`. -/
example (t : ℝ) : ‖LSeries 1 ((2 : ℝ) + t * I)‖ ≤ ∑' n, ‖LSeries.term 1 (2 : ℝ) n‖ := by
  have := (LSeriesSummable_one_iff.mpr (by norm_num : (1 : ℝ) < (2 : ℂ).re)).norm_vertical_le t
  simpa using this

example : Continuous fun t : ℝ => LSeries 1 ((2 : ℝ) + t * I) :=
  (LSeriesSummable_one_iff.mpr (by norm_num : (1 : ℝ) < (2 : ℂ).re)).continuous_vertical

/-- The term `n = 0` vanishes on every vertical line. -/
example (a : ℕ → ℂ) (c t : ℝ) : ‖LSeries.term a (c + t * I) 0‖ = 0 := by simp

end VerticalLineTest
