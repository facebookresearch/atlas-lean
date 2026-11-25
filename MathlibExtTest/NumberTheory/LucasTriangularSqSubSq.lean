/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasTriangularSqSubSq
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.lucasTriangular_sq_sub_sq

-- At the boundary the previous triangular number is the out-of-range coefficient (1 choose 2).
example (P : LucasParameters) : lucasnomial P 2 2 ^ 2 = 1 := by
  simpa [lucasnomial_eq_zero_of_lt P (by decide : 1 < 2), lucasBracket, lucasBracketAux,
    P.s_ne_zero] using lucasTriangular_sq_sub_sq P 0

-- Both the square weight and the denominator contribute for the parameters (2, 3).
example (P : LucasParameters) (hs : P.s = 2) (ht : P.t = 3) :
    lucasnomial P 3 2 ^ 2 - 9 * lucasnomial P 2 2 ^ 2 = 40 := by
  have h := lucasTriangular_sq_sub_sq P 1
  norm_num [lucasBracket, lucasBracketAux, hs, ht] at h
  exact h

end MetaMathlibExt.lucasTriangular_sq_sub_sq
