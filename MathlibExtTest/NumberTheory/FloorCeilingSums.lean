/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FloorCeilingSums
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The empty interval is allowed for every real input.
example (x : ℝ) : ∑ k ∈ Finset.Icc 1 (0 : ℕ), ⌈x + (k : ℝ) / (0 : ℕ)⌉ = 0 := by
  rw [sum_ceil_add_div_eq_ceil_mul_add]
  simp

-- A negative half-integer puts one summand exactly on an integer.
example : ∑ k ∈ Finset.Icc 1 (2 : ℕ), ⌈-(1 / 2 : ℝ) + (k : ℝ) / (2 : ℕ)⌉ = 1 := by
  rw [sum_ceil_add_div_eq_ceil_mul_add]
  norm_num

-- A nonintegral product rounds up even when it is negative.
example : ∑ k ∈ Finset.Icc 1 (3 : ℕ), ⌈-(1 / 2 : ℝ) + (k : ℝ) / (3 : ℕ)⌉ = 2 := by
  rw [sum_ceil_add_div_eq_ceil_mul_add]
  have h : ⌈(3 : ℝ) * -(1 / 2)⌉ = -1 := Int.ceil_eq_iff.mpr (by norm_num)
  norm_num [h]

example (F : ℝ → ℤ) (x : Fin 0 → ℝ) : inclExclLikeSum F x = 0 := by
  simp [inclExclLikeSum, Finset.eq_empty_of_isEmpty]

example (F : ℝ → ℤ) (a k : ℤ) : tverbergSum F ![a] 0 k = 0 := by
  simp [tverbergSum_one]
