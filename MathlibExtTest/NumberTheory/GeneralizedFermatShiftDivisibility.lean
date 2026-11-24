/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFermatShiftDivisibility

/-! # Tests for divisibility of later generalized Fermat numbers -/

open MetaMathlibExt

-- At n = 0, an odd exponent base preserves the divisor across a two-index shift.
example : 3 ∣ 2 ^ 3 ^ (0 + 2 : ℕ) + 1 :=
  (dvd_pow_pow_add_one_shift (a := 2) (b := 3) (D := 3) (n := 0)
    (ha := by decide) (hb := by decide) (hD := by decide) (h := by decide)).1
    (by decide) 2 (by decide)

-- An even exponent base loses the divisor 5, starting from the term at index 1.
example : ¬ 5 ∣ 2 ^ 2 ^ (1 + 1 : ℕ) + 1 :=
  (dvd_pow_pow_add_one_shift (a := 2) (b := 2) (D := 5) (n := 1)
    (ha := by decide) (hb := by decide) (hD := by decide) (h := by decide)).2
    even_two (by decide) 1 (by decide)

-- The even clause also applies at the smallest permitted modulus, D = 3.
example : ¬ 3 ∣ 2 ^ 2 ^ (0 + 2 : ℕ) + 1 :=
  (dvd_pow_pow_add_one_shift (a := 2) (b := 2) (D := 3) (n := 0)
    (ha := by decide) (hb := by decide) (hD := by decide) (h := by decide)).2
    even_two (by decide) 2 (by decide)

-- The counterexample from the docstring: divisibility by 2 persists despite even b.
example : (2 : ℕ) ∣ 3 ^ 2 ^ (0 : ℕ) + 1 ∧ (2 : ℕ) ∣ 3 ^ 2 ^ (0 + 1 : ℕ) + 1 := by
  decide
