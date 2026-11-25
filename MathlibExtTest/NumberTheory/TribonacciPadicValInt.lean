/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TribonacciPadicValInt
import Mathlib.Tactic.FinCases

open MetaMathlibExt

-- A negative shift by 47 periods from the representative with value -1.
example : padicValInt 47 (tribonacciInt (-2165) + 1) = 2 := by
  have h := tribonacci_padicValInt_fortySeven.2.1 (-3) (by decide) (-47) (by decide)
  rw [tribonacciInt_neg_three, sub_neg_eq_add] at h
  exact h.trans (congrArg (1 + ·) (padicValInt.self (by decide : 1 < 47)))

-- A shift by a square of the prime gives valuation three.
example : padicValInt 47 (tribonacciInt 101616 - 1) = 3 := by
  have h := tribonacci_padicValInt_fortySeven.2.1 2 (by decide) 2209 (by decide)
  rw [tribonacciInt_two] at h
  have : Fact (Nat.Prime 47) := ⟨by decide⟩
  exact h.trans (congrArg (1 + ·) (Nat.multiplicity_prime_pow (p := 47) 2))

-- At an index next to -7, both signs are excluded.
example : ¬ (47 : ℤ) ∣ tribonacciInt (-8) - 1 ∧ ¬ (47 : ℤ) ∣ tribonacciInt (-8) + 1 := by
  apply tribonacci_padicValInt_fortySeven.2.2
  intro j hj r
  fin_cases hj <;> omega
