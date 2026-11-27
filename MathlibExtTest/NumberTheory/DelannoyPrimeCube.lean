/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DelannoyPrimeCube

open MathlibExt.NumberTheory.DelannoyTriangleWanted MetaMathlibExt

-- At the first admissible prime, the Fermat quotient is 3 and the modulus is 125.
example : (ordinaryRiordanPascalLikeMatrix 10 5 1 : ZMod 125) = 58 ∧
    (ordinaryRiordanPascalLikeMatrix 9 4 1 : ZMod 125) = 56 := by
  obtain ⟨h, h'⟩ := delannoy_two_mul 5 (by decide) (by decide) (by decide)
  exact ⟨h.trans (by decide), h'.trans (by decide)⟩
