/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomProductEquationSubOne

/-!
# Tests for central binomial products in the case `x = a - 1`
-/

open MetaMathlibExt

-- At the smallest admissible value of `a`, the shift is two.
example (b : ℕ) (hb : 3 ≤ b) :
    (3 + b).centralBinom ≠ 20 * (2 + 2 * b).choose b := by
  simpa only [show (3 : ℕ).centralBinom = 20 by decide,
    show 3 + 2 * b - 1 = 2 + 2 * b by omega] using
    centralBinom_add_ne_centralBinom_mul_choose_sub_one 3 b (by decide) (by omega)

-- The upper bound on `2 * a` includes equality when `b = a`.
example (a : ℕ) (ha : 3 ≤ a) :
    (2 * a).centralBinom ≠ a.centralBinom * (3 * a - 1).choose a := by
  simpa only [show a + a = 2 * a by omega, show a + 2 * a = 3 * a by omega] using
    centralBinom_add_ne_centralBinom_mul_choose_sub_one a a (by omega) (by omega)

-- The product equals the central coefficient at the excluded endpoint `b = 0`.
example (a : ℕ) : (a + 0).centralBinom = a.centralBinom * (a + 2 * 0 - 1).choose 0 := by
  simp
