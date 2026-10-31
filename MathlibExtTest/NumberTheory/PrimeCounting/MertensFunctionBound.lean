/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.MertensFunctionBound

/-!
# Tests for the Mertens-function bound and squarefree counts
-/

@[expose] public section

open Asymptotics Filter ArithmeticFunction

example : ∃ c : ℝ, 0 < c ∧ (fun x : ℝ => (mertens x : ℝ))
    =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) :=
  mertens_isBigO_mul_exp_neg_mul_log_rpow

-- The squarefree numbers up to `10` are `1, 2, 3, 5, 6, 7, 10`.
example : ((Finset.Icc 1 10).filter Squarefree).card = 7 := by decide +kernel

-- Of these, `1, 6, 10` have an even number of prime factors.
example : ((Finset.Icc 1 10).filter
    (fun n => Squarefree n ∧ Even (ArithmeticFunction.cardFactors n))).card = 3 := by
  decide +kernel

example : (fun x : ℝ => (((Finset.Icc 1 ⌊x⌋₊).filter Squarefree).card : ℝ) - 6 / Real.pi ^ 2 * x)
    =O[atTop] fun x : ℝ => Real.sqrt x :=
  Nat.card_squarefree_sub_isBigO_sqrt

example : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => (((Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => Squarefree n ∧ Even (ArithmeticFunction.cardFactors n))).card : ℝ)
      - 3 / Real.pi ^ 2 * x)
    =O[atTop] fun x : ℝ => x * Real.exp (-c * Real.log x ^ (1 / 10 : ℝ)) :=
  Nat.card_squarefree_even_cardFactors_sub_isBigO
