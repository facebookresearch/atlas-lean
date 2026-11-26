/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.IntegerGroupDeterminantsC4SqProductModSixteen

/-!
# Tests for the circulant determinant product congruence on `C₄ × C₄`
-/

namespace MetaMathlibExt.C4SqProductModSixteenTest

private def evenIndexSumOdd (p : Fin 4 × Fin 4) : ℤ :=
  ![![1, 0, 0, 0], ![1, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 0, 0]] p.1 p.2

-- Here `b = (1, 1, 0, 1)` and `c = (1, 1, 2, 1)`: the cross terms add to 4.
example :
    circulantDetFour (c4SqB evenIndexSumOdd) * circulantDetFour (c4SqC evenIndexSumOdd) ≡
      1 [ZMOD 16] :=
  (c4Sq_circulantDetFour_product_mod_sixteen evenIndexSumOdd (by decide)).trans (by decide)

private def oddIndexSumOdd (p : Fin 4 × Fin 4) : ℤ :=
  ![![1, 0, 0, 0], ![2, -1, 0, 0], ![1, 0, 0, 0], ![2, 0, 0, 0]] p.1 p.2

-- Here `b = (1, 1, 1, 2)` and `c = (1, 3, 1, 2)`: the cross terms add to 10.
example :
    circulantDetFour (c4SqB oddIndexSumOdd) * circulantDetFour (c4SqC oddIndexSumOdd) ≡
      9 [ZMOD 16] :=
  (c4Sq_circulantDetFour_product_mod_sixteen oddIndexSumOdd (by decide)).trans (by decide)

end MetaMathlibExt.C4SqProductModSixteenTest
