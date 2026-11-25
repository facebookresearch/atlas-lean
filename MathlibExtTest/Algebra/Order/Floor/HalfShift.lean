/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Order.Floor.HalfShift
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- Even denominator: the half-shift lands exactly on an integer.
example : ⌊((2 : ℤ) : ℝ) / (4 : ℕ) + 1 / 2⌋ = 1 ∧
    ⌈((2 : ℤ) : ℝ) / (4 : ℕ) + 1 / 2⌉ = 1 := by
  obtain ⟨hf, hc⟩ := floor_ceil_div_add_half 2 4 (by decide)
  rw [hf, hc]
  norm_num [Int.floor_eq_iff, Int.ceil_eq_iff]

-- Odd denominator: 2q + m has remainder 1 modulo 2m, even for negative q.
example : ⌊((-4 : ℤ) : ℝ) / (3 : ℕ) + 1 / 2⌋ = -1 ∧
    ⌈((-4 : ℤ) : ℝ) / (3 : ℕ) + 1 / 2⌉ = 0 := by
  obtain ⟨hf, hc⟩ := floor_ceil_div_add_half (-4) 3 (by decide)
  rw [hf, hc]
  norm_num [Int.floor_eq_iff, Int.ceil_eq_iff]

-- Odd denominator: the other endpoint, remainder 2m - 1 modulo 2m.
example : ⌊((1 : ℤ) : ℝ) / (3 : ℕ) + 1 / 2⌋ = 0 ∧
    ⌈((1 : ℤ) : ℝ) / (3 : ℕ) + 1 / 2⌉ = 1 := by
  obtain ⟨hf, hc⟩ := floor_ceil_div_add_half 1 3 (by decide)
  rw [hf, hc]
  norm_num [Int.floor_eq_iff, Int.ceil_eq_iff]

-- With m = 1 the two shifted numerators differ by exactly one.
example : ⌊((-2 : ℤ) : ℝ) / (1 : ℕ) + 1 / 2⌋ = -2 ∧
    ⌈((-2 : ℤ) : ℝ) / (1 : ℕ) + 1 / 2⌉ = -1 := by
  obtain ⟨hf, hc⟩ := floor_ceil_div_add_half (-2) 1 (by decide)
  rw [hf, hc]
  norm_num [Int.floor_eq_iff, Int.ceil_eq_iff]
