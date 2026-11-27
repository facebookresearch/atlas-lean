/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Diophantine.Linear
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- A mixed-sign equation with a nontrivial gcd has step (3, 2).
example (x y : ℤ) : -6 * x + 9 * y - 12 = 0 ↔
    ∃ m : ℤ, x = 4 + m * 3 ∧ y = 4 + m * 2 := by
  have h := (linear_diophantine_solutions (-6) 9 (-12) 1 1 (by decide) (by decide)).1
    (by decide) x y
  norm_num [Int.gcd_def, sub_eq_add_neg] at h ⊢
  exact h

-- With zero first coefficient, the parameter ranges over the whole first coordinate.
example (x y : ℤ) : -5 * y + 10 = 0 ↔ ∃ m : ℤ, x = -m ∧ y = 2 := by
  have h := (linear_diophantine_solutions 0 (-5) 10 0 (-1) (by decide) (by decide)).1
    (by decide) x y
  norm_num [Int.gcd_def] at h ⊢
  exact h

-- The gcd is 3, so a constant term of 1 rules out every integer pair.
example (x y : ℤ) : 6 * x + 9 * y + 1 ≠ 0 :=
  (linear_diophantine_solutions 6 9 1 (-1) 1 (by decide) (by decide)).2 (by decide) x y
