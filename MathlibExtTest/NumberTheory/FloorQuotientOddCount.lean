/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FloorQuotientOddCount

open MetaMathlibExt

example : (∑ d ∈ Finset.Icc 1 0, ((0 / d : ℕ) : ℤ) * (-1) ^ (d + 1)) = 0 := by
  rw [← floorQuotientOddCount_eq_alternating_sum]
  decide

example : (∑ d ∈ Finset.Icc 1 10, ((10 / d : ℕ) : ℤ) * (-1) ^ (d + 1)) = 7 := by
  rw [← floorQuotientOddCount_eq_alternating_sum, floorQuotientOddCount_ten]
  rfl
