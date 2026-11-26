/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomProductEquationSubTwo

/-!
# Tests for central binomial products in the case `x = a - 2`
-/

open MetaMathlibExt

-- At the smallest admissible `a`, the shift is one.
example (b : ℕ) (hb : 3 ≤ b) :
    (3 + b).centralBinom ≠ 20 * (1 + 2 * b).choose b := by
  simpa only [show (3 : ℕ).centralBinom = 20 by decide,
    show 3 + 2 * b - 2 = 1 + 2 * b by omega] using
    centralBinom_add_ne_centralBinom_mul_choose_sub_two 3 b (by decide) (by omega)

-- The inequality has opposite directions at `a = 3` and `a = 4` for the same `b`.
example : (3 : ℕ).centralBinom * (9 : ℕ).choose 4 < (7 : ℕ).centralBinom := by decide
example : (8 : ℕ).centralBinom < (4 : ℕ).centralBinom * (10 : ℕ).choose 4 := by decide

-- The boundary `b = a` is included, even past the base case.
example (a : ℕ) (ha : 4 ≤ a) :
    (2 * a).centralBinom ≠ a.centralBinom * (3 * a - 2).choose a := by
  simpa only [show a + a = 2 * a by omega, show a + 2 * a = 3 * a by omega] using
    centralBinom_add_ne_centralBinom_mul_choose_sub_two a a (by omega) (by omega)

-- With `b = 0`, the strict inequality does not hold.
example (a : ℕ) : (a + 0).centralBinom = a.centralBinom * (a + 2 * 0 - 2).choose 0 := by
  simp
