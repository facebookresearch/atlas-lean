/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.HalfIntegerProgressions

open MetaMathlibExt

-- Denominator one and numerator zero give an integer step, including at index zero.
example (i : ℕ) : (1 / 2 : ℝ) + i * 2 ∉ Set.range ((↑) : ℕ → ℝ) :=
  add_mul_not_mem_nat_of_half _ _ 0 2 0 1 (by decide) (by simp) (by simp) i

-- The fractional part of the step need not be in lowest terms.
example (i : ℕ) : (3 + 1 / 2 : ℝ) + i * (3 / 9 : ℝ) ∉ Set.range ((↑) : ℕ → ℝ) :=
  add_mul_not_mem_nat_of_half _ _ 3 0 3 9 (by decide) (by simp) (by simp) i
