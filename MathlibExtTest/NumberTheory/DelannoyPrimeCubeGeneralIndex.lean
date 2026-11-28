/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DelannoyPrimeCubeGeneralIndex

open MathlibExt.NumberTheory.DelannoyTriangleWanted MetaMathlibExt

-- The boundary row `n = 1` has no nonconstant terms in the binomial sum.
example : (ordinaryRiordanPascalLikeMatrix 4 4 1 : ZMod 125) = 1 :=
  (delannoy_mul_sub_one 5 1 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

-- A noncentral entry at the first admissible prime.
example : (ordinaryRiordanPascalLikeMatrix 14 4 1 : ZMod 125) = 111 :=
  (delannoy_mul_sub_one 5 3 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

example : (ordinaryRiordanPascalLikeMatrix 27 6 1 : ZMod 343) = 134 :=
  (delannoy_mul_sub_one 7 4 (by decide) (by decide) (by decide) (by decide)).trans (by decide)
