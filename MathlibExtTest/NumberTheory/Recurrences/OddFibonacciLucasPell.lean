/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.OddFibonacciLucasPell

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

local notation "F₂" => generalizedFibonacciPolynomial 0 1 (C (4 : ℤ) * X) (C 2)
local notation "L₂" => generalizedFibonacciPolynomial 2 (C (4 : ℤ) * X) (C 4 * X) (C 2)

-- The squarefree specialization retains the named squarefreeness hypothesis.
example : ∃ n : ℕ, (2 : ℤ) ^ n * 44 = (L₂ (2 * n + 1)).eval 1 ∧
    (2 : ℤ) ^ n * 9 = (F₂ (2 * n + 1)).eval 1 :=
  fibLucas_odd_of_pell_eq_of_squarefree (a := 4) (b := 2) (P := 44) (Q := 9)
    (by decide) (by decide) (by decide) (hsq := Nat.squarefree_two) (by norm_num)

-- Check the initial pair (4, 1) and the next pair (44, 9), where the scale is 2.
example : (L₂ 1).eval 1 = 4 ∧ (F₂ 1).eval 1 = 1 ∧
    (L₂ 3).eval 1 = 2 * 44 ∧ (F₂ 3).eval 1 = 2 * 9 := by
  norm_num [generalizedFibonacciPolynomial]
