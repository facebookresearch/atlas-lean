/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DigitallyRobustComposites
import Mathlib.Tactic.NormNum

open MetaMathlibExt Polynomial

private theorem eval_cyclotomic_three : (cyclotomic 3 ℤ).eval 10 = 111 := by
  norm_num [cyclotomic_three]

-- The two prime factors of 111 exercise different conclusions at the same index.
example : orderOf (10 : ZMod 37) = 3 := by
  exact (cyclotomicPrimeDivisor_order_and_largestPrime 3 37 (by decide) (by decide)
    (by norm_num [eval_cyclotomic_three])).1 (by decide)

example : 3 ∣ 3 ∧ (∀ q : ℕ, q.Prime → q ∣ 3 → q ≤ 3) ∧ ¬ (3 : ℤ) ^ 2 ∣ 111 := by
  rw [← eval_cyclotomic_three]
  exact (cyclotomicPrimeDivisor_order_and_largestPrime 3 3 (by decide) (by decide)
    (by norm_num [eval_cyclotomic_three])).2 (by decide) (by decide)

-- Inserting an internal zero shifts the higher digits. Deleting it recovers the input.
example : insertDigit 101 1 0 = 1001 ∧ deleteDigit 1001 1 = 101 := by decide

-- Replacing the first leading zero extends the numeral by one digit.
example : replaceDigit 101 3 2 = 2101 := by decide
