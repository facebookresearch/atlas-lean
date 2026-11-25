/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomProductEquationOne

/-!
# Tests for central binomial products with shift one
-/

open MetaMathlibExt

example (b : ℕ) (hb : 0 < b) : (1 + b).centralBinom = 2 * (1 + 2 * b).choose b :=
  (centralBinom_add_eq_centralBinom_mul_choose_one_iff 1 b (by decide) hb).2 rfl

example (b : ℕ) (hb : 0 < b) : (2 + b).centralBinom ≠ 6 * (1 + 2 * b).choose b := by
  intro h
  exact (by decide : (2 : ℕ) ≠ 1)
    ((centralBinom_add_eq_centralBinom_mul_choose_one_iff 2 b (by decide) hb).1 h)

-- At the excluded endpoint `b = 0`, every `a` gives equality.
example (a : ℕ) : (a + 0).centralBinom = a.centralBinom * (1 + 2 * 0).choose 0 := by
  simp
