/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GeneralPellBisectorsRatSolution

namespace MathlibExtTest.NumberTheory.GeneralPellBisectorsRatSolution

open MetaMathlibExt

-- A zero slope is allowed over the rationals. The common square-free factor is `1`.
example :
    let a : ℚ := 0
    let b : ℚ := 3 / 4
    let c : ℚ := 1 / 3
    let d : ℕ := 1
    let a₂ : ℚ := 1
    let b₂ : ℚ := 5 / 4
    |a| ≠ |b| ∧ (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) ∧
      0 < d ∧ Squarefree d ∧ a ^ 2 - d * a₂ ^ 2 = -1 ∧ b ^ 2 - d * b₂ ^ 2 = -1 ∧
      b₂ + a₂ ≠ 0 ∧ c = (a * b₂ + a₂ * b) / (b₂ + a₂) := by
  dsimp only
  norm_num [squarefree_one]

-- Hirotsu's Example 1 has `d = 2`. With positive second coordinates the two fractions give the
-- two bisector slopes `2` and `-1/2`; check each formula independently.
example :
    let a : ℚ := 1
    let b : ℚ := 7
    let d : ℕ := 2
    let a₂ : ℚ := 1
    let b₂ : ℚ := 5
    let c₁ : ℚ := 2
    let c₂ : ℚ := -1 / 2
    |a| ≠ |b| ∧ 0 < d ∧ Squarefree d ∧ a ^ 2 - d * a₂ ^ 2 = -1 ∧ b ^ 2 - d * b₂ ^ 2 = -1 ∧
      (a - c₁) ^ 2 * (b ^ 2 + 1) = (b - c₁) ^ 2 * (a ^ 2 + 1) ∧
      (a - c₂) ^ 2 * (b ^ 2 + 1) = (b - c₂) ^ 2 * (a ^ 2 + 1) ∧
      b₂ + a₂ ≠ 0 ∧ c₁ = (a * b₂ + a₂ * b) / (b₂ + a₂) ∧
      b₂ - a₂ ≠ 0 ∧ c₂ = (a * b₂ - a₂ * b) / (b₂ - a₂) := by
  dsimp only
  norm_num [Nat.prime_two.squarefree]

-- A client can obtain the witnesses from the bisector equation with no Pell-solution input.
example :
    let a : ℚ := 1
    let b : ℚ := 7
    let c : ℚ := 2
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ ∃ a₂ b₂ : ℚ, a ^ 2 - d * a₂ ^ 2 = -1 ∧
      b ^ 2 - d * b₂ ^ 2 = -1 ∧
      ((b₂ + a₂ ≠ 0 ∧ c = (a * b₂ + a₂ * b) / (b₂ + a₂)) ∨
        (b₂ - a₂ ≠ 0 ∧ c = (a * b₂ - a₂ * b) / (b₂ - a₂))) :=
  bisector_equation_rat_solution 1 7 2 (by norm_num) (by norm_num)

end MathlibExtTest.NumberTheory.GeneralPellBisectorsRatSolution
