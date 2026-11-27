/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomProductEquationLeTen

/-!
# Tests for central binomial products with index sum at most ten
-/

open MetaMathlibExt

-- Equality still holds at the largest admissible sum when both parameters are one.
example : (10 : ℕ).centralBinom = (1 : ℕ).centralBinom * (19 : ℕ).choose 9 :=
  (centralBinom_add_eq_centralBinom_mul_choose_iff_of_le_ten 1 1 9 (by decide) (by decide)
    (by decide) (by decide)).2 ⟨rfl, rfl⟩

-- With the same sum, taking b = 1 and a = 9 rules out every positive shift.
example (x : ℕ) (hx : 0 < x) : (10 : ℕ).centralBinom ≠ (9 : ℕ).centralBinom * (x + 2).choose 1 := by
  intro h
  have ha := ((centralBinom_add_eq_centralBinom_mul_choose_iff_of_le_ten x 9 1 hx (by decide)
    (by decide) (by decide)).1 h).2
  omega
