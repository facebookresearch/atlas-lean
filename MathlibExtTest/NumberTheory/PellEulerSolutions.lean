/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellEulerSolutions
import Mathlib.Tactic.LinearCombination

namespace MetaMathlibExt.pell_euler_solutions

/-- The fundamental solution `3 + 2√2` of `x² - 2y² = 1`, with `d` written as `a * b` for
`a = 1` and `b = 2`. -/
private def threeTwo : Pell.Solution₁ (1 * 2) := Pell.Solution₁.mk 3 2 (by norm_num)

-- No solution of `x² - 2y² = 1` has `x = 2`, so `3 + 2√2` is fundamental.
private theorem threeTwo_isFundamental : Pell.IsFundamental threeTwo := by
  refine ⟨by simp [threeTwo], by simp [threeTwo], fun {s} hs => ?_⟩
  rw [threeTwo, Pell.Solution₁.x_mk]
  by_contra! h
  have hs2 : s.x = 2 := by omega
  have hp := s.prop
  rw [hs2] at hp
  omega

-- The family through `(1, 1)` for `T² - 2U² = -1` continues with `(7, 5)` and `(41, 29)`.
example :
    (1 * (threeTwo ^ 1).x + 2 * 1 * (threeTwo ^ 1).y,
        1 * 1 * (threeTwo ^ 1).y + 1 * (threeTwo ^ 1).x) = (7, 5) ∧
      (1 * (threeTwo ^ 2).x + 2 * 1 * (threeTwo ^ 2).y,
        1 * 1 * (threeTwo ^ 2).y + 1 * (threeTwo ^ 2).x) = (41, 29) := by
  simp [sq, threeTwo, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]

-- Each member of that family solves the equation.
example (j : ℕ) :
    1 * (1 * (threeTwo ^ j).x + 2 * 1 * (threeTwo ^ j).y) ^ 2 -
      2 * (1 * 1 * (threeTwo ^ j).y + 1 * (threeTwo ^ j).x) ^ 2 = -1 :=
  (pell_euler_solutions 1 2 (-1) 1 1 (by norm_num) threeTwo_isFundamental.d_nonsquare
    (by norm_num) (by norm_num) threeTwo threeTwo_isFundamental).1 j

-- The negative Pell equation `T² - 2U² = -1` has infinitely many integer solutions.
example : {p : ℤ × ℤ | p.1 ^ 2 - 2 * p.2 ^ 2 = -1}.Infinite := by
  obtain ⟨hsol, hinj⟩ := pell_euler_solutions 1 2 (-1) 1 1 (by norm_num)
    threeTwo_isFundamental.d_nonsquare (by norm_num) (by norm_num) threeTwo
    threeTwo_isFundamental
  exact Set.infinite_of_injective_forall_mem hinj fun j => by simpa using hsol j

-- Both coefficients may be negative: `-2T² + 3U² = 1` has infinitely many integer solutions.
example : {p : ℤ × ℤ | -2 * p.1 ^ 2 + 3 * p.2 ^ 2 = 1}.Infinite := by
  -- `5 + 2√6` solves `x² - 6y² = 1` with `x > 1`, so `6` is not a square.
  have hsq : ¬ IsSquare (-2 * -3 : ℤ) :=
    Pell.Solution₁.d_nonsquare_of_one_lt_x (a := .mk 5 2 (by norm_num)) (by simp)
  obtain ⟨ε, hε⟩ := Pell.IsFundamental.exists_of_not_isSquare (by norm_num) hsq
  obtain ⟨hsol, hinj⟩ := pell_euler_solutions (-2) (-3) 1 1 1 (by norm_num) hsq (by norm_num)
    (by norm_num) ε hε
  refine Set.infinite_of_injective_forall_mem hinj fun j => ?_
  simp only [Set.mem_ofPred_eq]
  linear_combination hsol j

-- Without `c ≠ 0` injectivity fails: the family through `(0, 0)` is constant.
example (ε : Pell.Solution₁ (1 * 2)) :
    ¬ Function.Injective fun j : ℕ =>
      (0 * (ε ^ j).x + 2 * 0 * (ε ^ j).y, 1 * 0 * (ε ^ j).y + 0 * (ε ^ j).x) := by
  intro h
  exact absurd (@h 0 1 (by simp)) (by decide)

end MetaMathlibExt.pell_euler_solutions
