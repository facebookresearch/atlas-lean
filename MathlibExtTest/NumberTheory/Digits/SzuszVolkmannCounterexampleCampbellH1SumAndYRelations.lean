/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexampleCampbellH1SumAndYRelations

/-! # Tests for sums of `h₁` and jumps of `h₂` at powers of ten -/

namespace MathlibExtTest.NumberTheory.Digits.SzuszVolkmannCounterexampleCampbellH1SumAndYRelations

open MetaMathlibExt

-- At `ℓ = 1` the sum over `1, …, 99` is `900`.
example : ∑ i ∈ Finset.Icc 1 99, campbellH1 i = 900 := by
  have h := campbellH1_sum_and_y_relations.1 1 le_rfl
  have e1 : (10 : ℕ) ^ (1 + 1) - 1 = 99 := by norm_num
  have hrhs : (∑ j ∈ Finset.range 1, 900 * 100 ^ j) = 900 := by decide
  rw [e1, hrhs] at h
  exact h

-- At `ℓ = 2` the sum over `1, …, 999` is `90900`.
example : ∑ i ∈ Finset.Icc 1 999, campbellH1 i = 90900 := by
  have h := campbellH1_sum_and_y_relations.1 2 (by norm_num)
  have e1 : (10 : ℕ) ^ (2 + 1) - 1 = 999 := by norm_num
  have hrhs : (∑ j ∈ Finset.range 2, 900 * 100 ^ j) = 90900 := by decide
  rw [e1, hrhs] at h
  exact h

-- At `ℓ = 2` the slope across the block `10, …, 99` is `10`.
example : ((campbellH2 99 : ℚ) - campbellH2 10) / (9 * 10 - 1) = 10 := by
  have h := (campbellH1_sum_and_y_relations.2 2 (by norm_num)).1
  have e1 : (10 : ℕ) ^ 2 - 1 = 99 := by norm_num
  have e2 : (2 : ℕ) - 1 = 1 := by norm_num
  rw [e1, e2] at h
  simpa using h

-- At `ℓ = 2` the jump at `100` is `100`.
example : (campbellH2 100 : ℤ) - campbellH2 99 = 100 := by
  have h := (campbellH1_sum_and_y_relations.2 2 (by norm_num)).2
  have e1 : (10 : ℕ) ^ 2 - 1 = 99 := by norm_num
  have e2 : 2 * (2 / 2) = 2 := by norm_num
  rw [e1, e2] at h
  norm_num at h
  exact h

-- At `ℓ = 3` the jump at `1000` is `10 ^ (2 * (3 / 2)) = 100`, not `10 ^ 3`.
example : (campbellH2 1000 : ℤ) - campbellH2 999 = 100 := by
  have h := (campbellH1_sum_and_y_relations.2 3 (by norm_num)).2
  have e1 : (10 : ℕ) ^ 3 - 1 = 999 := by norm_num
  have e2 : 2 * (3 / 2) = 2 := by norm_num
  have e3 : (10 : ℕ) ^ 3 = 1000 := by norm_num
  rw [e1, e3, e2] at h
  exact h.trans (by norm_num)

end MathlibExtTest.NumberTheory.Digits.SzuszVolkmannCounterexampleCampbellH1SumAndYRelations
