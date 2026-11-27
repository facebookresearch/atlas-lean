/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCountingFromDivisors

open Finset MetaMathlibExt

-- At the lower endpoint, the only term counts the prime 2 exactly.
example : 0 < 1 / (Real.exp 3 * (Real.exp 1 - 1)) := by
  have h := primeCountingApprox_sub_lt 2 (hn := by decide)
  have hIcc : Icc 2 (2 : ℕ) = {2} := by decide
  have hdiv : (2 : ℕ).divisors.card = 2 := by decide
  have hcount : Nat.primeCounting 2 = 1 := by decide
  simpa [hIcc, hdiv, hcount] using h

-- At 4, the two prime terms cancel and 4 contributes the full weight exp (-4).
example : Real.exp (-4) < 1 / (Real.exp 3 * (Real.exp 1 - 1)) := by
  have h := primeCountingApprox_sub_lt 4 (hn := by decide)
  have hIcc : Icc 2 (4 : ℕ) = {2, 3, 4} := by decide
  have hdiv₂ : (2 : ℕ).divisors.card = 2 := by decide
  have hdiv₃ : (3 : ℕ).divisors.card = 2 := by decide
  have hdiv₄ : (4 : ℕ).divisors.card = 3 := by decide
  have hcount : Nat.primeCounting 4 = 2 := by decide
  norm_num [hIcc, hdiv₂, hdiv₃, hdiv₄, hcount, sum_insert] at h ⊢
  linarith only [h]
