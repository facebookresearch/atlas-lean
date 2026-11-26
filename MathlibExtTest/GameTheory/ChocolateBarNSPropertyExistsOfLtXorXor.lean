/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtXorXor

namespace MathlibExtTest.GameTheory.ChocolateBarNSPropertyExistsOfLtXorXor

open MetaMathlibExt

-- With constant bounds ten, one is below the nim-sum of three, four and five.
example : (∃ u < 3, 1 = u ^^^ 4 ^^^ 5) ∨ (∃ v < 4, 1 = 3 ^^^ v ^^^ 5) ∨
    ∃ w < 5, 1 = min 10 3 ^^^ min 10 4 ^^^ w :=
  HasNSProperty.exists_of_lt_xor_xor (hasNSProperty_const 10) (hasNSProperty_const 10)
    (by decide) (by decide) (by decide)

-- Halving bounds still admit the mex step at two, one and six.
example : (∃ u < 2, 4 = u ^^^ 1 ^^^ 6) ∨ (∃ v < 1, 4 = 2 ^^^ v ^^^ 6) ∨
    ∃ w < 6, 4 = min (w / 2 ^ 1) 2 ^^^ min 5 1 ^^^ w :=
  HasNSProperty.exists_of_lt_xor_xor (hasNSProperty_div_two_pow (m := 1) (by decide))
    (hasNSProperty_const 5) (by decide) (by decide) (by decide)

end MathlibExtTest.GameTheory.ChocolateBarNSPropertyExistsOfLtXorXor
