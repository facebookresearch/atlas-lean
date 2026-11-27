/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.OddFibonacciLucasPell
import Mathlib.Tactic.NormNum

open MetaMathlibExt Polynomial

local notation "F" => generalizedFibonacciPolynomial 0 1 (C (8 : ℤ) * X) (C 4)
local notation "L" => generalizedFibonacciPolynomial 2 (C (8 : ℤ) * X) (C 8 * X) (C 4)

-- For a nonsquarefree b strictly dividing a, this solution takes two descent steps.
example : ∃ n : ℕ, (4 : ℤ) ^ n * 2728 = (L (2 * n + 1)).eval 1 ∧
    (4 : ℤ) ^ n * 305 = (F (2 * n + 1)).eval 1 := by
  apply fibLucas_odd_of_pell_eq (a := 8) (b := 4) (P := 2728) (Q := 305)
    (by decide) (by decide) (by decide)
  norm_num

-- At indices one and five the scale factors are respectively one and sixteen.
example : (L 1).eval 1 = 8 ∧ (F 1).eval 1 = 1 ∧
    (L 5).eval 1 = 4 ^ 2 * 2728 ∧ (F 5).eval 1 = 4 ^ 2 * 305 := by
  norm_num [generalizedFibonacciPolynomial]
