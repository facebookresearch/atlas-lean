/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasPolytopicNumberHasSumInvLucasBracketMulSucc
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Absolute summability of reciprocal products of Lucas brackets

The sum formula implies absolute summability of the reciprocal-product series.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 13.
-/

namespace MathlibExtTest.NumberTheory.LucasPolytopicNumberHasSumInvLucasBracketMulSucc

open MetaMathlibExt

example (P : LucasParameters) (hs : 0 < P.s) (hdisc : 0 < P.s ^ 2 + 4 * P.t)
    (ht : 1 < |P.t|) :
    Summable (fun n : ℕ => |1 / (lucasBracket P (n + 1) * lucasBracket P (n + 2))|) :=
  (hasSum_inv_lucasBracket_mul_succ P hs hdisc ht).summable.abs

end MathlibExtTest.NumberTheory.LucasPolytopicNumberHasSumInvLucasBracketMulSucc
