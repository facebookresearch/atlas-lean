/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.CirculantDetFourCongruences

/-!
# Tests for congruences of the four-by-four circulant determinant
-/

open MetaMathlibExt

-- Odd `m` and odd `k + l + n`, with nonzero entries in both patterns.
example :
    circulantDetFour ![(-3 : ℤ), 2, -6, 4] ≡ 9 [ZMOD 16] ∧
      circulantDetFour ![(-4 : ℤ), 3, -5, 5] ≡ 5 [ZMOD 16] := by
  have h := circulantDetFour_mod_sixteen (-2) 1 (-3) 2
  exact ⟨h.1.trans (by decide), h.2.trans (by decide)⟩

-- Even `m` and even `k + l + n`, again with negative and positive entries.
example :
    circulantDetFour ![(3 : ℤ), -4, 4, -6] ≡ 1 [ZMOD 16] ∧
      circulantDetFour ![(2 : ℤ), -3, 5, -5] ≡ 13 [ZMOD 16] := by
  have h := circulantDetFour_mod_sixteen 1 (-2) 2 (-3)
  exact ⟨h.1.trans (by decide), h.2.trans (by decide)⟩
