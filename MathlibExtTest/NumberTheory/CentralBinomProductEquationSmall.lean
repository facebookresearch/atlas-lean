/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomProductEquationSmall

/-!
# Tests for central binomial products with a bounded index sum
-/

open MetaMathlibExt

-- With `a = 6` and `b = 12`, the product crosses the central coefficient between shifts 2 and 3.
example : (18 : ℕ).centralBinom ≠ (6 : ℕ).centralBinom * (26 : ℕ).choose 12 :=
  centralBinom_add_ne_of_two_le_of_small 2 6 12 (by decide) (by decide) (by decide)
    (by decide) (by decide)

example : (18 : ℕ).centralBinom ≠ (6 : ℕ).centralBinom * (27 : ℕ).choose 12 :=
  centralBinom_add_ne_of_two_le_of_small 3 6 12 (by decide) (by decide) (by decide)
    (by decide) (by decide)

-- The largest admissible sum and shift, for every positive decomposition of 149.
example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hsum : a + b = 149) :
    (149 : ℕ).centralBinom ≠ a.centralBinom * (148 + 2 * b).choose b := by
  rw [← hsum]
  exact centralBinom_add_ne_of_two_le_of_small 148 a b (by decide) ha hb (by omega) (by omega)
