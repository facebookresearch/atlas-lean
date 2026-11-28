/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Diophantine.BisectorEquationPythagorean

/-! # Tests for the Pythagorean parametrization of rational bisector slopes -/

namespace MathlibExtTest.NumberTheory.Diophantine.BisectorEquationPythagorean

-- Hirotsu's Example 3(a): check the shared parameters and both bisector slopes directly.
example :
    let a : ℚ := 3 / 4
    let b : ℚ := 12 / 5
    let c₁ : ℚ := 9 / 7
    let c₂ : ℚ := -7 / 9
    let l : ℤ := 2
    let m : ℤ := 5
    let n : ℤ := 1
    |a| ≠ |b| ∧ a ^ 2 - (5 / 4 : ℚ) ^ 2 = -1 ∧ b ^ 2 - (13 / 5 : ℚ) ^ 2 = -1 ∧
      (a - c₁) ^ 2 * (b ^ 2 + 1) = (b - c₁) ^ 2 * (a ^ 2 + 1) ∧
      (a - c₂) ^ 2 * (b ^ 2 + 1) = (b - c₂) ^ 2 * (a ^ 2 + 1) ∧
      |l| ≠ |m| ∧ l * m ≠ n ^ 2 ∧ l * m * n ≠ 0 ∧
      a = ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n) ∧ b = ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n) ∧
      c₁ = ((l : ℚ) * m - n ^ 2) / ((l + m) * n) ∧ c₂ = -(((l : ℚ) + m) * n) / (l * m - n ^ 2) := by
  dsimp only
  norm_num

-- A zero slope is allowed; here `l / n = 1` and `m / n = 3 / 2` need a shared denominator of `2`.
example :
    let a : ℚ := 0
    let b : ℚ := 5 / 12
    let c : ℚ := -5
    let l : ℤ := 2
    let m : ℤ := 3
    let n : ℤ := 2
    |a| ≠ |b| ∧ a ^ 2 - (1 : ℚ) ^ 2 = -1 ∧ b ^ 2 - (13 / 12 : ℚ) ^ 2 = -1 ∧
      (a - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (a ^ 2 + 1) ∧
      |l| ≠ |m| ∧ l * m ≠ n ^ 2 ∧ l * m * n ≠ 0 ∧
      a = ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n) ∧ b = ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n) ∧
      c = -(((l : ℚ) + m) * n) / (l * m - n ^ 2) := by
  dsimp only
  norm_num

-- The public API accepts signed rational square-root witnesses.
example :
    let a : ℚ := 0
    let b : ℚ := 5 / 12
    let c : ℚ := -5
    ∃ l m n : ℤ, |l| ≠ |m| ∧ l * m ≠ n ^ 2 ∧ l * m * n ≠ 0 ∧
      a = ((l : ℚ) ^ 2 - n ^ 2) / (2 * l * n) ∧ b = ((m : ℚ) ^ 2 - n ^ 2) / (2 * m * n) ∧
      (c = ((l : ℚ) * m - n ^ 2) / ((l + m) * n) ∨ c = -(((l : ℚ) + m) * n) / (l * m - n ^ 2)) :=
  MetaMathlibExt.bisector_equation_rat_solution_pythagorean 0 (5 / 12) (-5)
    (by norm_num) (by norm_num) ⟨-1, by norm_num⟩ ⟨13 / 12, by norm_num⟩

end MathlibExtTest.NumberTheory.Diophantine.BisectorEquationPythagorean
