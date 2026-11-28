/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PolygonalNumber
public import MathlibExt.NumberTheory.PolygonalSumParity
public import MathlibExt.NumberTheory.PracticalNumber
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.PracticalPolygonalSums
public import MathlibExt.NumberTheory.PolygonalSumModPrimePow
public import MathlibExt.NumberTheory.OddSquareTriangular
public import MathlibExt.NumberTheory.PracticalPolygonalSumsPracticalAddPolygonalExceptions
public import MathlibExt.NumberTheory.PracticalPolygonalSumsExistsSqAddSqModEqPrimePow
public import MathlibExt.NumberTheory.PracticalPolygonalSumsIsPracticalNumberMulOfLeSigmaAddOne
public import MathlibExt.NumberTheory.PracticalPolygonalSumsEventuallyTwo
public import MathlibExt.NumberTheory.PracticalPolygonalSumsExistsPracticalAddTriangular

/-!
# Sums of practical numbers and polygonal numbers

Statements from Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and
Polygonal Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1
(arXiv:2403.13533). The statement `MetaMathlibExt.exists_sq_add_sq_modEq_prime_pow` is in
`MathlibExt.NumberTheory.PracticalPolygonalSumsExistsSqAddSqModEqPrimePow`. In the paper
"natural number" means positive integer; practical numbers
are `MetaMathlibExt.IsPracticalNumber`. The paper's `s`-gonal number `P_s(n)` is the canonical
`Nat.polygonalNumber s n`; triangular numbers are `Nat.polygonalNumber 3 k = k (k + 1) / 2`
with `k ≥ 0` (the paper's Lemma 5, arXiv Lemma 3.3, counts `0`).
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction
open scoped Nat

end

end MetaMathlibExt
