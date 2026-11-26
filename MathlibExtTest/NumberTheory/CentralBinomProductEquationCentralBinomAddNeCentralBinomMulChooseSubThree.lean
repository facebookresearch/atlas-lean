/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomProductEquationCentralBinomAddNeCentralBinomMulChooseSubThree

/-!
# Tests for central binomial products with shift `a - 3`

These examples instantiate the theorem at the small indices and the change of inequality direction.
-/

namespace MathlibExtTest.NumberTheory

namespace CentralBinomProductEquationCentralBinomAddNeCentralBinomMulChooseSubThree

example : (3 + 3).centralBinom ≠
    (3 : ℕ).centralBinom * (3 + 2 * 3 - 3).choose 3 := by
  exact MetaMathlibExt.centralBinom_add_ne_centralBinom_mul_choose_sub_three 3 3
    (by decide) (by decide)

example : (4 + 4).centralBinom ≠
    (4 : ℕ).centralBinom * (4 + 2 * 4 - 3).choose 4 := by
  exact MetaMathlibExt.centralBinom_add_ne_centralBinom_mul_choose_sub_three 4 4
    (by decide) (by decide)

example : (5 + 5).centralBinom ≠
    (5 : ℕ).centralBinom * (5 + 2 * 5 - 3).choose 5 := by
  exact MetaMathlibExt.centralBinom_add_ne_centralBinom_mul_choose_sub_three 5 5
    (by decide) (by decide)

example : (5 + 58).centralBinom ≠
    (5 : ℕ).centralBinom * (5 + 2 * 58 - 3).choose 58 := by
  exact MetaMathlibExt.centralBinom_add_ne_centralBinom_mul_choose_sub_three 5 58
    (by decide) (by decide)

example : (5 + 59).centralBinom ≠
    (5 : ℕ).centralBinom * (5 + 2 * 59 - 3).choose 59 := by
  exact MetaMathlibExt.centralBinom_add_ne_centralBinom_mul_choose_sub_three 5 59
    (by decide) (by decide)

example : (6 + 6).centralBinom ≠
    (6 : ℕ).centralBinom * (6 + 2 * 6 - 3).choose 6 := by
  exact MetaMathlibExt.centralBinom_add_ne_centralBinom_mul_choose_sub_three 6 6
    (by decide) (by decide)

end CentralBinomProductEquationCentralBinomAddNeCentralBinomMulChooseSubThree

end MathlibExtTest.NumberTheory
