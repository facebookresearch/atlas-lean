/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PythagoreanTripleGroupsPythagoreanCathetusProduct

/-! # Tests for `MathlibExt.NumberTheory.PythagoreanTripleGroupsPythagoreanCathetusProduct` -/

namespace MathlibExtTest.NumberTheory.PythagoreanTripleGroupsPythagoreanCathetusProduct

open MetaMathlibExt

-- The parameters `1 ∈ C(3)` and `2 ∈ C(4)` generate `(3, 4, 5)` and `(4, 3, 5)`; the product
-- parameter lies in `C(12)`.
example : 1 * 2 ∈ amatoCathetusParams (3 * 4) :=
  (pythagorean_cathetus_product 3 4 1 2 (by norm_num) (by norm_num)
    one_mem_amatoCathetusParams_three two_mem_amatoCathetusParams_four).2.2.2.2

-- The product equations `y = a₁ * b₂ + a₂ * b₁` and `z = a₁ * b₁ + a₂ * b₂` at `1 ∈ C(3)`
-- and `2 ∈ C(4)`.
example : (((3 : ℚ) * 4) ^ 2 / (2 * (1 * 2)) - 1 * 2 / 2
      = ((3 : ℚ) ^ 2 / (2 * 1) - 1 / 2) * ((4 : ℚ) ^ 2 / (2 * 2) + 2 / 2)
        + ((3 : ℚ) ^ 2 / (2 * 1) + 1 / 2) * ((4 : ℚ) ^ 2 / (2 * 2) - 2 / 2))
    ∧ (((3 : ℚ) * 4) ^ 2 / (2 * (1 * 2)) + 1 * 2 / 2
      = ((3 : ℚ) ^ 2 / (2 * 1) - 1 / 2) * ((4 : ℚ) ^ 2 / (2 * 2) - 2 / 2)
        + ((3 : ℚ) ^ 2 / (2 * 1) + 1 / 2) * ((4 : ℚ) ^ 2 / (2 * 2) + 2 / 2)) := by
  obtain ⟨h1, -, -, h4, -⟩ :=
    pythagorean_cathetus_product 3 4 1 2 (by norm_num) (by norm_num)
      one_mem_amatoCathetusParams_three two_mem_amatoCathetusParams_four
  refine ⟨?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h4

end MathlibExtTest.NumberTheory.PythagoreanTripleGroupsPythagoreanCathetusProduct
