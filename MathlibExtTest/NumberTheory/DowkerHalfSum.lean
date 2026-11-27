/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DowkerHalfSum

open MetaMathlibExt

-- Both endpoints of the empty-sum convention.
example : watsonAlternatingCosecantSum 0 = 0 := by
  simp [watsonAlternatingCosecantSum]

example : watsonAlternatingCosecantSum 1 = 0 := by
  simp [watsonAlternatingCosecantSum]

-- The first nonempty odd sum cancels, while the preceding even sum has one term.
example : watsonAlternatingCosecantSum 3 = 0 :=
  watson_alternating_odd_zero 3 (by decide)

example : watsonAlternatingCosecantSum 2 ≠ 0 := by
  rw [watsonAlternatingCosecantSum_two]
  norm_num

-- At order zero, natural subtraction gives a zeroth derivative and a vanishing coefficient.
example (n ν : ℕ) : watsonOddCotangentDeriv 0 n ν = Real.cot (Real.pi * ν / n) := by
  simp [watsonOddCotangentDeriv]

example (n ν : ℕ) : watsonExpansionTerm 0 n ν = 0 := by
  simp [watsonExpansionTerm]

example (n : ℕ) : watsonAlternatingMain 1 n = 2 * (n : ℝ) * Real.log 2 / Real.pi := by
  simp [watsonAlternatingMain]
