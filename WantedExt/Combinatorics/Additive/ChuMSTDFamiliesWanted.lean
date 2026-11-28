/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chu et al.'s families of MSTD sets

Statements from Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a
New Family of MSTD Sets*, INTEGERS 24 (2024), Article A32.

Sets are written by their sequence of consecutive differences (Spohn's notation, Theorem 5's
notation paragraph): `(a₁ | g₁, …, g_r)` is `{a₁, a₁ + g₁, a₁ + g₁ + g₂, …}`, and
`M^k` is the difference sequence `1, 4, …, 4, 3` with `k` fours. A set `A` is MSTD
(sum-dominated) when `|A + A| > |A - A|`, balanced when `|A + A| = |A - A|`, and
difference-dominated when `|A + A| < |A - A|`; a family has one of these properties when
every member has it.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyDifferenceDominated
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdIncreasing
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardAdd
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardSubSixAddFourMul
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdDecreasing
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTAddSupsetSixFamilies

namespace MetaMathlibExt

@[expose] public section

open Pointwise

end

end MetaMathlibExt
