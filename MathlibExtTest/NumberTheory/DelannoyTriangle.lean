/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DelannoyTriangle

namespace MathlibExtTest.NumberTheory.DelannoyTriangle

open MathlibExt.NumberTheory.DelannoyTriangleWanted MetaMathlibExt

-- At p = 3 the double sum equals the Legendre symbol (2 / 3) = -1.
example : (∑ n ∈ Finset.range 3, ∑ k ∈ Finset.range (n + 1),
    (ordinaryRiordanPascalLikeMatrix n k 1 : ZMod 3)) = -1 := by
  rw [sum_delannoy 3 (by decide)]
  decide

-- Hence the double sum at p = 3 squares to 1.
example : (∑ n ∈ Finset.range 3, ∑ k ∈ Finset.range (n + 1),
    (ordinaryRiordanPascalLikeMatrix n k 1 : ZMod 3)) ^ 2 = 1 := by
  rw [sum_delannoy 3 (by decide)]
  decide

end MathlibExtTest.NumberTheory.DelannoyTriangle
